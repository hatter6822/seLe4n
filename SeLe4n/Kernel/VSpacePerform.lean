-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API

/-!
# Address-space operations, split into their checks and their writes

WS-ZA ZA5.4.  The frame map and unmap, the instruction-cache unify and the
page-table install and removal as seL4 splits an invocation: every check is read
from the state first (`…AdmittedAt`), and an admitted operation is its writes
(`…PerformAt`), each in the object's own slot: a root through
`storeVSpaceRootWith`, a frame through `storeFrameWith`, a page table through
`storePageTableWith`, a capability's mapping record through `storeCNodeWith`.
Each `…_of_admitted` theorem is the obligation the dispatcher's
`RefusalCarrying.ofChecked` arm discharges: an admitted operation succeeds as
its writes.  A ledger entry a write owes is read back from the object as stored
after the write (`mappedRootLedger`, `rootSlotLedger`, `detachedSlotLedger`),
equal to the specification's because the page tables it reads are unchanged.

The checks are each operation's own refusals, plus the ones its stores need to
be in-slot writes on every table, well-formed or not: the ASID table names the
root for its ASID (frame map and unmap), and the object table finds each object
written where it stands (`RHTable.findsInPlace`).  A state where one of these
fails runs the specification instead (`RefusalCarrying.ofChecked`), so none
refuses an operation the specification admits.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Architecture.SyscallArgDecode

/-- WS-ZA ZA5.4: the root a frame mapping leaves (`VSpaceRoot.mapPage`'s insert). -/
@[inline] def rootWithMapping (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) (r : VSpaceRoot) : VSpaceRoot :=
  { r with mappings := r.mappings.insert vaddr (paddr, perms) }

/-- WS-ZA ZA5.4: the root a mapping's epoch tag leaves (`tagFrameMapping`). -/
@[inline] def rootWithEpoch (vaddr : SeLe4n.VAddr) (epoch : Nat) (r : VSpaceRoot) :
    VSpaceRoot :=
  { r with mappingEpochs := r.mappingEpochs.insert vaddr epoch }

/-- WS-ZA ZA5.4: the frame a mapping's epoch tag leaves: its counter advanced. -/
@[inline] def frameWithNextEpoch (f : FrameObject) : FrameObject :=
  { f with mapEpoch := f.mapEpoch + 1 }

/-- WS-ZA ZA5.4: the frame's map epoch, read as a word. -/
@[inline] def frameMapEpochOf (st : SystemState) (frameId : SeLe4n.ObjId) : Nat :=
  match st.getFrame? frameId with
  | some f => f.mapEpoch
  | none => 0

/-- WS-ZA ZA5.4: the descriptor store a map records (`mappingStore?`), read
from the root as stored after the mapping. -/
@[inline] def mappedRootLedger (st : SystemState) (rootId : SeLe4n.ObjId)
    (vaddr : SeLe4n.VAddr) : List Architecture.PhysicalWrite :=
  match st.getVSpaceRoot? rootId with
  | some r => (Architecture.mappingStore? st r vaddr).toList
  | none => []

/-- WS-ZA ZA5.4: the capability's mapping record written in its CNode slot —
`cspaceRecordFrameMappingImpl`'s write, total. -/
@[inline] def recordFrameMappingAt (st : SystemState) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (m : FrameMapping) : SystemState :=
  match st.getCNode? cnode with
  | some cn =>
    match cn.lookup slot with
    | some cap => st.storeCNodeWith cnode (·.insert slot { cap with mapping := some m })
    | none => st
  | none => st

/-- WS-ZA ZA5.4: **the map's address-space step, written in place** — the
mapping in the root's slot, its descriptor store on the ledger, the executing
core's flush, drain and fill (`vspaceMapPageCheckedWithShootdownFromStatePerCore`
on an admitted fresh map). -/
@[inline] def vspaceMapStepAt (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (rootId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  let st1 := st.storeVSpaceRootWith rootId (rootWithMapping vaddr paddr perms)
  let st1 := Architecture.recordPhysicalWrites st1 (mappedRootLedger st1 rootId vaddr)
  let st2 := { st1 with tlb := adapterFlushTlbByVAddr st1.tlb asid vaddr }
  Architecture.tlbFillOnCore
    (Architecture.drainInitiatorPerCoreView st2 ec [Architecture.encodePageInvalidation asid vaddr])
    ec asid vaddr

/-- WS-ZA ZA5.4: **an admitted frame map's writes**, each in its object's slot:
the address-space step, the epoch tag in the root and the frame, and the record
on the capability. -/
def vspaceMapPerformAt (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (rootId frameId cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) :
    SystemState :=
  let st3 := vspaceMapStepAt ec asid vaddr paddr perms rootId st
  let epoch := frameMapEpochOf st3 frameId
  let st4 := st3.storeVSpaceRootWith rootId (rootWithEpoch vaddr epoch)
  let st5 := st4.storeFrameWith frameId frameWithNextEpoch
  recordFrameMappingAt st5 cnode slot { asid := asid, vaddr := vaddr, epoch := epoch }

/-- WS-ZA ZA5.4: **the frame map's checks**, read from the state before any
write: `vspaceMapFromFrameCap`'s refusals past the frame resolution, the
address-space step's (`vspaceMapPageCheckedWithFlushFromState`), and the
in-place conditions (see the module docstring).  `rootId` is the root the
invoked capability names, which the dispatcher's authorisation check resolved
for `args.asid`. -/
def vspaceMapAdmittedAt (st : SystemState) (args : VSpaceMapArgs) (frameCap : Capability)
    (frame : FrameObject) (rootId : SeLe4n.ObjId) : Bool :=
  (match frameMappingAdmissible frameCap frame args.perms with
   | .ok () => true
   | .error _ => false) &&
  args.vaddr.inUserWindow &&
  !capabilityMappingLive st frameCap &&
  Architecture.asidTranslationReady st args.asid args.vaddr &&
  (match validateVSpaceMapPermsForMemoryKind frame.base args.perms st.machine.memoryMap with
   | .ok _ => true
   | .error _ => false) &&
  args.vaddr.isCanonical &&
  decide (frame.base.toNat < 2 ^ st.machine.physicalAddressWidth) &&
  frame.base.toNat % Architecture.pageBytes == 0 &&
  args.perms.wxCompliant &&
  Architecture.pageMappingAligned args.vaddr frame.base &&
  (match st.getVSpaceRoot? rootId with
   | some root => root.asid == args.asid && (root.mappings[args.vaddr]?).isNone
   | none => false) &&
  st.asidTable.holds args.asid rootId &&
  st.objects.findsInPlace rootId &&
  st.objects.findsInPlace (frameCapObjId frameCap)

-- ============================================================================
-- An admitted map is its writes
-- ============================================================================

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

/-- A fresh, aligned, W^X-compliant mapping is `rootWithMapping`. -/
theorem mapPage_eq_rootWithMapping {root : VSpaceRoot} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions} (hWx : perms.wxCompliant = true)
    (hAl : Architecture.pageMappingAligned vaddr paddr = true)
    (hF : root.mappings[vaddr]? = none) :
    root.mapPage vaddr paddr perms = some (rootWithMapping vaddr paddr perms root) := by
  unfold Architecture.pageMappingAligned at hAl
  simp only [Bool.and_eq_true, beq_iff_eq, Architecture.pageBytes] at hAl
  unfold VSpaceRoot.mapPage
  simp [hWx, hAl.1, hAl.2, hF, rootWithMapping]

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

open SeLe4n.Kernel.RobinHood in
/-- **The address-space step of an admitted map is `vspaceMapStepAt`**: a fresh
map posts no shootdown, and its root store is the in-slot write. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_eq_stepAt
    (ec : Concurrency.CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (rootId : SeLe4n.ObjId)
    (root : VSpaceRoot) (st : SystemState)
    (hR : st.objects[rootId]? = some (.vspaceRoot root)) (hAs : root.asid = asid)
    (hH : st.asidTable.holds asid rootId = true) (hF : root.mappings[vaddr]? = none)
    (hWx : perms.wxCompliant = true) (hAl : Architecture.pageMappingAligned vaddr paddr = true)
    (hCanon : vaddr.isCanonical = true)
    (hBound : paddr.toNat < 2 ^ st.machine.physicalAddressWidth)
    (hPg : paddr.toNat % Architecture.pageBytes = 0) (hIn : st.objects.findsInPlace rootId = true) :
    Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore ec asid vaddr paddr perms st
      = .ok ((), vspaceMapStepAt ec asid vaddr paddr perms rootId st) := by
  have hRes := resolveAsidRoot_of_holds hH hR hAs
  have hFresh : Architecture.vspaceHasTranslation st asid vaddr = false := by
    unfold Architecture.vspaceHasTranslation
    rw [hRes]
    simp [VSpaceRoot.lookup, hF]
  have hMap := mapPage_eq_rootWithMapping (root := root) hWx hAl hF
  let f := rootWithMapping vaddr paddr perms
  have hf : (f root).asid = root.asid := rfl
  let st1 := st.storeVSpaceRootWith rootId f
  -- the ledger the specification records is the one read back from the stored root
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
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
  rw [Architecture.vspaceMapPageCheckedWithShootdownFromState_fresh_inert _ _ _ _ _ _ hFresh]
  unfold Architecture.vspaceMapPageCheckedWithFlushFromState
  simp only [hCanon, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hBound, decide_true,
    hPg, bne_self_eq_false]
  unfold Architecture.vspaceMapPageWithFlush Architecture.vspaceMapPage
  rw [hRes]
  simp only [hWx, hAl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hMap]
  rw [hStore]
  rfl

open SeLe4n.Kernel.RobinHood in
/-- **The epoch tag of an admitted map is its two in-slot writes**: the epoch
beside the translation in the root, the counter advanced in the frame. -/
theorem tagFrameMapping_eq_inSlot (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (rootId frameId : SeLe4n.ObjId) (st : SystemState) (root : VSpaceRoot) (fr : FrameObject)
    (hR : st.objects[rootId]? = some (.vspaceRoot root)) (hAs : root.asid = asid)
    (hH : st.asidTable.holds asid rootId = true) (hFr : st.objects[frameId]? = some (.frame fr))
    (hIn : st.objects.findsInPlace rootId = true) (hNe : rootId ≠ frameId) :
    tagFrameMapping asid vaddr frameId st =
      .ok (fr.mapEpoch, (st.storeVSpaceRootWith rootId (rootWithEpoch vaddr fr.mapEpoch)).storeFrameWith
        frameId frameWithNextEpoch) := by
  have hRes := resolveAsidRoot_of_holds hH hR hAs
  have hG : st.getFrame? frameId = some fr := by simp only [SystemState.getFrame?, hFr]
  have hS1 := SystemState.storeObject_vspaceRoot_eq_storeVSpaceRootWith hR
    (rootWithEpoch vaddr fr.mapEpoch) rfl
  have hFr4 : (st.storeVSpaceRootWith rootId (rootWithEpoch vaddr fr.mapEpoch)).objects[frameId]?
      = some (.frame fr) := by
    rw [SystemState.storeVSpaceRootWith_objects hR _ rfl, RHTable_getElem?_eq_get?,
      RHTable.get?_insert_ne_of_findsInPlace _ _ hIn hNe]
    exact hFr
  have hS2 := SystemState.storeObject_frame_eq_storeFrameWith hFr4 frameWithNextEpoch
  unfold tagFrameMapping
  rw [hG, hRes]
  dsimp only
  rw [show (KernelObject.vspaceRoot { root with mappingEpochs := root.mappingEpochs.insert vaddr fr.mapEpoch })
      = .vspaceRoot (rootWithEpoch vaddr fr.mapEpoch root) from rfl, hS1]
  dsimp only
  rw [show (KernelObject.frame { fr with mapEpoch := fr.mapEpoch + 1 })
      = .frame (frameWithNextEpoch fr) from rfl, hS2]

/-- **The record of an admitted map is its in-slot write.** -/
theorem cspaceRecordFrameMapping_eq_recordAt (st : SystemState) (addr : CSpaceAddr)
    (m : FrameMapping) (cn : CNode) (cap : Capability)
    (hC : st.objects[addr.cnode]? = some (.cnode cn)) (hL : cn.lookup addr.slot = some cap) :
    cspaceRecordFrameMapping addr m st = .ok ((), recordFrameMappingAt st addr.cnode addr.slot m) := by
  rw [cspaceRecordFrameMapping_eq_impl]
  unfold cspaceRecordFrameMappingImpl recordFrameMappingAt
  rw [(SystemState.getCNode?_eq_some_iff st addr.cnode cn).2 hC]
  simp only [hL]

/-- The address-space step writes only the root among the objects, and keeps
the ASID table. -/
theorem vspaceMapStepAt_objects (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (rootId : SeLe4n.ObjId) (st : SystemState) :
    (vspaceMapStepAt ec asid vaddr paddr perms rootId st).objects =
        (st.storeVSpaceRootWith rootId (rootWithMapping vaddr paddr perms)).objects ∧
      (vspaceMapStepAt ec asid vaddr paddr perms rootId st).asidTable =
        (st.storeVSpaceRootWith rootId (rootWithMapping vaddr paddr perms)).asidTable := by
  unfold vspaceMapStepAt
  have h := Architecture.tlbFillOnCore_frame
    (Architecture.drainInitiatorPerCoreView
      { Architecture.recordPhysicalWrites (st.storeVSpaceRootWith rootId (rootWithMapping vaddr paddr perms))
          (mappedRootLedger (st.storeVSpaceRootWith rootId (rootWithMapping vaddr paddr perms)) rootId vaddr) with
        tlb := adapterFlushTlbByVAddr
          (Architecture.recordPhysicalWrites (st.storeVSpaceRootWith rootId (rootWithMapping vaddr paddr perms))
            (mappedRootLedger (st.storeVSpaceRootWith rootId (rootWithMapping vaddr paddr perms)) rootId vaddr)).tlb
          asid vaddr }
      ec [Architecture.encodePageInvalidation asid vaddr]) ec asid vaddr
  exact ⟨h.1, h.2.1⟩

open SeLe4n.Kernel.RobinHood in
/-- **WS-ZA ZA5.4: an admitted frame map is its writes.**  The obligation the
dispatcher's `RefusalCarrying.ofChecked` arm discharges: past the frame
resolution, the checks `vspaceMapAdmittedAt` reads are every refusal
`vspaceMapFromFrameCap` can make, and the map then runs as
`vspaceMapPerformAt`, each store in its object's slot. -/
theorem vspaceMapFromFrameCap_of_admitted (tid : SeLe4n.ThreadId) (ec : Concurrency.CoreId)
    (args : VSpaceMapArgs) (st : SystemState) (frameSlot : CSpaceAddr) (frameCap : Capability)
    (frame : FrameObject) (rootId : SeLe4n.ObjId)
    (hRes : resolveVSpaceMapFrame tid args st = .ok (frameSlot, frameCap, frame))
    (hA : vspaceMapAdmittedAt st args frameCap frame rootId = true) :
    vspaceMapFromFrameCap tid ec args st =
      .ok ((), vspaceMapPerformAt ec args.asid args.vaddr frame.base args.perms rootId
        (frameCapObjId frameCap) frameSlot.cnode frameSlot.slot st) := by
  obtain ⟨_, _, frameObjId, _, _, _, _, hTgt, hFrame, _, hSlot⟩ :=
    resolveVSpaceMapFrame_ok_authorised tid args st frameSlot frameCap frame hRes
  have hFid : frameCapObjId frameCap = frameObjId := by unfold frameCapObjId; rw [hTgt]
  have hFr : st.objects[frameObjId]? = some (.frame frame) :=
    (SystemState.getFrame?_eq_some_iff st frameObjId frame).1 hFrame
  unfold vspaceMapAdmittedAt at hA
  cases hFA : frameMappingAdmissible frameCap frame args.perms with
  | error e => simp [hFA] at hA
  | ok u =>
  cases u
  cases hV : validateVSpaceMapPermsForMemoryKind frame.base args.perms st.machine.memoryMap with
  | error e => simp [hV] at hA
  | ok p =>
  have hP := validateVSpaceMapPermsForMemoryKind_ok_eq _ _ _ _ hV
  subst hP
  cases hGR : st.getVSpaceRoot? rootId with
  | none => simp [hGR] at hA
  | some root =>
  have hR : st.objects[rootId]? = some (.vspaceRoot root) :=
    (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).1 hGR
  simp only [hFA, hV, hGR, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
    beq_iff_eq, decide_eq_true_eq, Option.isNone_iff_eq_none, hFid] at hA
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hWin, hLive⟩, hReady⟩, -⟩, hCanon⟩, hBound⟩, hPg⟩, hWx⟩, hAl⟩,
    ⟨hAs, hFresh⟩⟩, hH⟩, hInR⟩, hInF⟩ := hA
  have hNe : rootId ≠ frameObjId := by
    intro h; rw [h, hFr] at hR; cases hR
  -- the address-space step
  have hStep := vspaceMapPageCheckedWithShootdownFromStatePerCore_eq_stepAt ec args.asid args.vaddr
    frame.base args.perms rootId root st hR hAs hH hFresh hWx hAl hCanon hBound hPg hInR
  let f := rootWithMapping args.vaddr frame.base args.perms
  let st3 := vspaceMapStepAt ec args.asid args.vaddr frame.base args.perms rootId st
  obtain ⟨hO3, hA3⟩ := vspaceMapStepAt_objects ec args.asid args.vaddr frame.base args.perms rootId st
  have hO3' : st3.objects = st.objects.insert rootId (.vspaceRoot (f root)) := by
    rw [hO3, SystemState.storeVSpaceRootWith_objects hR f rfl]
  have hA3' : st3.asidTable = st.asidTable := by
    rw [hA3, SystemState.storeVSpaceRootWith_asidTable hR f rfl (hAs ▸ hH)]
  have hR3 : st3.objects[rootId]? = some (.vspaceRoot (f root)) := by
    rw [hO3', RHTable_getElem?_eq_get?, RHTable.get?_insert_self_of_findsInPlace _ hInR]
  have hFr3 : st3.objects[frameObjId]? = some (.frame frame) := by
    rw [hO3', RHTable_getElem?_eq_get?, RHTable.get?_insert_ne_of_findsInPlace _ _ hInR hNe]
    exact hFr
  have hInAfterStep : st3.objects.findsInPlace rootId = true := by
    rw [hO3', RHTable.findsInPlace_insert_of_findsInPlace _ _ hInR]; exact hInR
  have hH3 : st3.asidTable.holds args.asid rootId = true := by rw [hA3']; exact hH
  have hTag := tagFrameMapping_eq_inSlot args.asid args.vaddr rootId frameObjId st3 (f root) frame
    hR3 hAs hH3 hFr3 hInAfterStep hNe
  have hEpoch : frameMapEpochOf st3 frameObjId = frame.mapEpoch := by
    unfold frameMapEpochOf; simp only [SystemState.getFrame?, hFr3]
  -- the record
  let st4 := st3.storeVSpaceRootWith rootId (rootWithEpoch args.vaddr frame.mapEpoch)
  let st5 := st4.storeFrameWith frameObjId frameWithNextEpoch
  have hO4 : st4.objects = st3.objects.insert rootId
      (.vspaceRoot (rootWithEpoch args.vaddr frame.mapEpoch (f root))) :=
    SystemState.storeVSpaceRootWith_objects hR3 _ rfl
  have hFr4 : st4.objects[frameObjId]? = some (.frame frame) := by
    rw [hO4, RHTable_getElem?_eq_get?, RHTable.get?_insert_ne_of_findsInPlace _ _ hInAfterStep hNe]
    exact hFr3
  have hInF4 : st4.objects.findsInPlace frameObjId = true := by
    rw [hO4, RHTable.findsInPlace_insert_of_findsInPlace _ _ hInAfterStep, hO3',
      RHTable.findsInPlace_insert_of_findsInPlace _ _ hInR]
    exact hInF
  have hO5 : st5.objects = st4.objects.insert frameObjId (.frame (frameWithNextEpoch frame)) :=
    SystemState.storeFrameWith_objects hFr4 _
  obtain ⟨cn, hCn, hLk⟩ : ∃ cn, st.objects[frameSlot.cnode]? = some (.cnode cn) ∧
      cn.lookup frameSlot.slot = some frameCap := by
    unfold SystemState.lookupSlotCap at hSlot
    cases hC : SystemState.lookupCNode st frameSlot.cnode with
    | none => rw [hC] at hSlot; cases hSlot
    | some cn =>
      rw [hC] at hSlot
      refine ⟨cn, ?_, hSlot⟩
      unfold SystemState.lookupCNode at hC
      split at hC
      · next c hx => cases hC; exact hx
      · cases hC
  have hCR : frameSlot.cnode ≠ rootId := by intro h; rw [h, hR] at hCn; cases hCn
  have hCF : frameSlot.cnode ≠ frameObjId := by intro h; rw [h, hFr] at hCn; cases hCn
  have hCn5 : st5.objects[frameSlot.cnode]? = some (.cnode cn) := by
    rw [hO5, RHTable_getElem?_eq_get?,
      RHTable.get?_insert_ne_of_findsInPlace _ _ hInF4 (Ne.symm hCF), hO4,
      RHTable.get?_insert_ne_of_findsInPlace _ _ hInAfterStep (Ne.symm hCR), hO3',
      RHTable.get?_insert_ne_of_findsInPlace _ _ hInR (Ne.symm hCR)]
    exact hCn
  have hRec := cspaceRecordFrameMapping_eq_recordAt st5 frameSlot
    { asid := args.asid, vaddr := args.vaddr, epoch := frame.mapEpoch } cn frameCap hCn5 hLk
  -- the arm
  unfold vspaceMapFromFrameCap
  rw [hRes]
  dsimp only
  rw [hFA]
  dsimp only
  simp only [hWin, hLive, hReady, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hV]
  dsimp only
  rw [hStep]
  dsimp only
  rw [hFid, hTag]
  dsimp only
  rw [hRec]
  unfold vspaceMapPerformAt
  simp only [show frameMapEpochOf (vspaceMapStepAt ec args.asid args.vaddr frame.base args.perms
    rootId st) frameObjId = frame.mapEpoch from hEpoch]
  rfl


-- ============================================================================
-- The frame unmap
-- ============================================================================

/-- WS-ZA ZA5.4: the root an unmap leaves (`VSpaceRoot.unmapPage`'s erase). -/
@[inline] def rootWithoutMapping (vaddr : SeLe4n.VAddr) (r : VSpaceRoot) : VSpaceRoot :=
  { r with mappings := r.mappings.erase vaddr }

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
  let st4 := Architecture.drainInitiatorPerCoreView st3 ec
    [Architecture.encodePageInvalidation asid vaddr]
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

-- ============================================================================
-- The instruction-cache unify
-- ============================================================================

/-- WS-ZA ZA5.4: **the unify's checks**: the ASID resolves and maps `vaddr`
(`vspaceUnifyInstructionPage`'s two refusals). -/
def vspaceUnifyAdmittedAt (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    Bool :=
  match Architecture.resolveAsidRoot st asid with
  | some (_, root) => (VSpaceRoot.lookup root vaddr).isSome
  | none => false

/-- WS-ZA ZA5.4: **an admitted unify's writes**: the domain-wide invalidate and
its record on the emission ledger.  The identity when the checks refuse. -/
def vspaceUnifyPerformAt (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (st : SystemState) :
    SystemState :=
  match Architecture.resolveAsidRoot st asid with
  | some (_, root) =>
    match VSpaceRoot.lookup root vaddr with
    | some (paddr, _) =>
      Architecture.recordIcacheMaintenance
        (Architecture.icInvalidateBroadcast st Architecture.icBroadcastReach (.unifyPage paddr))
        (.unifyPage paddr)
    | none => st
  | none => st

/-- **WS-ZA ZA5.4: an admitted unify is its writes.** -/
theorem vspaceUnifyInstructionPage_of_admitted (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st : SystemState) (hA : vspaceUnifyAdmittedAt st asid vaddr = true) :
    Architecture.vspaceUnifyInstructionPage asid vaddr st =
      .ok ((), vspaceUnifyPerformAt asid vaddr st) := by
  unfold vspaceUnifyAdmittedAt at hA
  unfold Architecture.vspaceUnifyInstructionPage vspaceUnifyPerformAt
  cases hR : Architecture.resolveAsidRoot st asid with
  | none => simp [hR] at hA
  | some p =>
    obtain ⟨_, root⟩ := p
    simp only [hR] at hA ⊢
    cases hL : VSpaceRoot.lookup root vaddr with
    | none => simp [hL] at hA
    | some e => rfl

-- ============================================================================
-- The page-table map and unmap
-- ============================================================================

/-- The parent entry's store reads only the page tables, so two states with
the same page tables agree on it. -/
theorem slotStore?_congr {s t : SystemState}
    (h : ∀ id, s.getPageTable? id = t.getPageTable? id) (r : VSpaceRoot) (level index : Nat) :
    Architecture.slotStore? s r level index = Architecture.slotStore? t r level index := by
  unfold Architecture.slotStore? Architecture.tablePageAt?
  simp only [h]

/-- WS-ZA ZA5.4: the level `.pageTableMap` installs at — the shallowest the
walk to `vaddr` misses — read as a word (`0` when the root is absent or the walk
is complete; the checks refuse both). -/
@[inline] def pageTableMapLevelAt (st : SystemState) (rootId : SeLe4n.ObjId)
    (vaddr : SeLe4n.VAddr) : Nat :=
  match st.getVSpaceRoot? rootId with
  | some root =>
    match root.missingLevel? vaddr with
    | some level => level
    | none => 0
  | none => 0

/-- WS-ZA ZA5.4: the parent entry's store a table install or removal records
(`slotStore?`), read from the root as stored after the write. -/
@[inline] def rootSlotLedger (st : SystemState) (rootId : SeLe4n.ObjId) (level index : Nat) :
    List Architecture.PhysicalWrite :=
  match st.getVSpaceRoot? rootId with
  | some r => (Architecture.slotStore? st r level index).toList
  | none => []

/-- WS-ZA ZA5.4: **an admitted table install's writes**, each in its object's
slot: the install record in the table, the slot in the root, and the parent
entry's store on the ledger (`pageTableMap`). -/
def pageTableMapPerformAt (tableId rootId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr)
    (st : SystemState) : SystemState :=
  let level := pageTableMapLevelAt st rootId vaddr
  let index := PageTableSlot.indexOf level vaddr
  let st1 := st.storePageTableWith tableId (·.installedAt rootId level index)
  let st2 := st1.storeVSpaceRootWith rootId (·.withTableSlot level index tableId)
  Architecture.recordPhysicalWrites st2 (rootSlotLedger st2 rootId level index)

/-- WS-ZA ZA5.4: **the table install's checks**, read before any write:
`pageTableMap`'s refusals, and the object table finding the table and the root
where they stand (`RHTable.findsInPlace`). -/
def pageTableMapAdmittedAt (st : SystemState) (tableId rootId : SeLe4n.ObjId)
    (vaddr : SeLe4n.VAddr) : Bool :=
  (match st.getPageTable? tableId with
   | some _ => true
   | none => false) &&
  (match st.getVSpaceRoot? rootId with
   | some root => root.tableBase.isSome && (root.missingLevel? vaddr).isSome
   | none => false) &&
  !Architecture.pageTableInstallLive st tableId &&
  Architecture.pageTableAddressable vaddr &&
  st.objects.findsInPlace tableId &&
  st.objects.findsInPlace rootId

open SeLe4n.Kernel.RobinHood in
/-- A root slot written in place after a table store: the specification's store
of the root over the recorded parent entry is the in-slot write followed by the
entry read back from the stored root. -/
theorem storeObject_root_slot_eq_inSlot {st1 : SystemState} {rootId : SeLe4n.ObjId}
    {root : VSpaceRoot} (hR1 : st1.objects[rootId]? = some (.vspaceRoot root))
    (hInAfterTable : st1.objects.findsInPlace rootId = true) (f : VSpaceRoot → VSpaceRoot)
    (hf : (f root).asid = root.asid) (level index : Nat) (extra : VSpaceRoot → List Architecture.PhysicalWrite) :
    storeObject rootId (.vspaceRoot (f root))
      (Architecture.recordPhysicalWrites st1
        ((Architecture.slotStore? st1 (f root) level index).toList ++ extra (f root))) =
      .ok ((), Architecture.recordPhysicalWrites (st1.storeVSpaceRootWith rootId f)
        (match (st1.storeVSpaceRootWith rootId f).getVSpaceRoot? rootId with
         | some r => (Architecture.slotStore? (st1.storeVSpaceRootWith rootId f) r level index).toList
             ++ extra r
         | none => [])) := by
  have hObj2 : (st1.storeVSpaceRootWith rootId f).objects[rootId]? = some (.vspaceRoot (f root)) := by
    rw [SystemState.storeVSpaceRootWith_objects hR1 f hf, RHTable_getElem?_eq_get?,
      RHTable.get?_insert_self_of_findsInPlace _ hInAfterTable]
  rw [show (st1.storeVSpaceRootWith rootId f).getVSpaceRoot? rootId = some (f root) by
    simp only [SystemState.getVSpaceRoot?, hObj2]]
  dsimp only
  rw [← slotStore?_congr (storeVSpaceRootWith_getPageTable? hR1 hInAfterTable f hf),
    ← storeVSpaceRootWith_recordPhysicalWrites]
  exact SystemState.storeObject_vspaceRoot_eq_storeVSpaceRootWith
    (st := Architecture.recordPhysicalWrites st1 _) hR1 f hf

open SeLe4n.Kernel.RobinHood in
/-- **WS-ZA ZA5.4: an admitted table install is its writes.** -/
theorem pageTableMap_of_admitted (tableId rootId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr)
    (st : SystemState) (hA : pageTableMapAdmittedAt st tableId rootId vaddr = true) :
    Architecture.pageTableMap tableId rootId vaddr st =
      .ok ((), pageTableMapPerformAt tableId rootId vaddr st) := by
  unfold pageTableMapAdmittedAt at hA
  cases hGT : st.getPageTable? tableId with
  | none => simp [hGT] at hA
  | some table =>
  cases hGR : st.getVSpaceRoot? rootId with
  | none => simp [hGR] at hA
  | some root =>
  have hT : st.objects[tableId]? = some (.pageTable table) :=
    (SystemState.getPageTable?_eq_some_iff st tableId table).1 hGT
  have hR : st.objects[rootId]? = some (.vspaceRoot root) :=
    (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).1 hGR
  simp only [hGT, hGR, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
    Option.isSome_iff_exists] at hA
  obtain ⟨⟨⟨⟨⟨hTB, level, hM⟩, hLive⟩, hAddr⟩, hInT⟩, hInR⟩ := hA
  have hNe : tableId ≠ rootId := by intro h; rw [h, hR] at hT; cases hT
  have hLv : pageTableMapLevelAt st rootId vaddr = level := by
    unfold pageTableMapLevelAt; rw [hGR]; dsimp only; rw [hM]
  let index := PageTableSlot.indexOf level vaddr
  let st1 := st.storePageTableWith tableId (·.installedAt rootId level index)
  have hS1 : storeObject tableId (.pageTable (table.installedAt rootId level index)) st =
      .ok ((), st1) :=
    SystemState.storeObject_pageTable_eq_storePageTableWith hT
      (fun t => t.installedAt rootId level index)
  have hO1 : st1.objects = st.objects.insert tableId (.pageTable (table.installedAt rootId level index)) :=
    SystemState.storePageTableWith_objects hT (fun t => t.installedAt rootId level index)
  have hR1 : st1.objects[rootId]? = some (.vspaceRoot root) := by
    rw [hO1, RHTable_getElem?_eq_get?, RHTable.get?_insert_ne_of_findsInPlace _ _ hInT hNe]
    exact hR
  have hInAfterTable : st1.objects.findsInPlace rootId = true := by
    rw [hO1, RHTable.findsInPlace_insert_of_findsInPlace _ _ hInT]; exact hInR
  have hS2 := storeObject_root_slot_eq_inSlot hR1 hInAfterTable
    (fun r => r.withTableSlot level index tableId) rfl level index (fun _ => [])
  simp only [List.append_nil] at hS2
  have hTB' : root.tableBase.isNone = false := by
    cases h : root.tableBase <;> simp_all
  unfold Architecture.pageTableMap
  rw [hGT, hGR]
  dsimp only
  simp only [hLive, hTB', hAddr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hM]
  rw [hS1]
  dsimp only
  rw [hS2]
  unfold pageTableMapPerformAt rootSlotLedger
  rw [hLv]

/-- WS-ZA ZA5.4: the table's record once it is installed nowhere. -/
@[inline] def tableUninstalled (t : PageTableObject) : PageTableObject :=
  { t with installedIn := none }

/-- WS-ZA ZA5.4: the parent entry's store and the ASID invalidate a table's
removal records (`pageTableUnmap`), read from the root as stored after the
write. -/
@[inline] def detachedSlotLedger (st : SystemState) (inst : PageTableInstall) :
    List Architecture.PhysicalWrite :=
  match st.getVSpaceRoot? inst.root with
  | some r => (Architecture.slotStore? st r inst.level inst.index).toList ++ [.invalidateAsid r.asid]
  | none => []

/-- WS-ZA ZA5.4: **an admitted table removal's writes**, each in its object's
slot: the record cleared in the table and, when the root still holds the table,
the slot removed from the root with its parent entry's store and the ASID
invalidate on the ledger (`pageTableUnmap`).  Whether the root holds the table
is read before the first write. -/
def pageTableUnmapPerformAt (tableId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  match st.getPageTable? tableId with
  | some table =>
    match table.installedIn with
    | some inst =>
      let live := Architecture.pageTableInstallLive st tableId
      let st1 := st.storePageTableWith tableId tableUninstalled
      if live then
        let st2 := st1.storeVSpaceRootWith inst.root (·.withoutTableSlot inst tableId)
        Architecture.recordPhysicalWrites st2 (detachedSlotLedger st2 inst)
      else st1
    | none => st
  | none => st

/-- WS-ZA ZA5.4: **the table removal's checks**, read before any write:
`pageTableUnmap`'s refusals (no table; a table still in use), and the object
table finding the table, and the root it is removed from, where they stand. -/
def pageTableUnmapAdmittedAt (st : SystemState) (tableId : SeLe4n.ObjId) : Bool :=
  match st.getPageTable? tableId with
  | some table =>
    st.objects.findsInPlace tableId &&
    (match table.installedIn with
     | some inst =>
       match st.getVSpaceRoot? inst.root with
       | some root =>
         !root.tables.contains (inst.slotFor tableId) ||
           (!Architecture.pageTableInUse root inst && st.objects.findsInPlace inst.root)
       | none => true
     | none => true)
  | none => false

open SeLe4n.Kernel.RobinHood in
/-- **WS-ZA ZA5.4: an admitted table removal is its writes.** -/
theorem pageTableUnmap_of_admitted (tableId : SeLe4n.ObjId) (st : SystemState)
    (hA : pageTableUnmapAdmittedAt st tableId = true) :
    Architecture.pageTableUnmap tableId st = .ok ((), pageTableUnmapPerformAt tableId st) := by
  unfold pageTableUnmapAdmittedAt at hA
  cases hGT : st.getPageTable? tableId with
  | none => simp [hGT] at hA
  | some table =>
  have hT : st.objects[tableId]? = some (.pageTable table) :=
    (SystemState.getPageTable?_eq_some_iff st tableId table).1 hGT
  have hS1 : storeObject tableId (.pageTable { table with installedIn := none }) st =
      .ok ((), st.storePageTableWith tableId tableUninstalled) :=
    SystemState.storeObject_pageTable_eq_storePageTableWith hT tableUninstalled
  simp only [hGT, Bool.and_eq_true] at hA
  obtain ⟨hInT, hA⟩ := hA
  unfold Architecture.pageTableUnmap pageTableUnmapPerformAt
  rw [hGT]
  dsimp only
  cases hI : table.installedIn with
  | none => rfl
  | some inst =>
  dsimp only
  have hLiveEq : Architecture.pageTableInstallLive st tableId =
      (st.getVSpaceRoot? inst.root).any (·.tables.contains (inst.slotFor tableId)) := by
    unfold Architecture.pageTableInstallLive; rw [hGT]; dsimp only; rw [hI]
  rw [hLiveEq]
  cases hGR : st.getVSpaceRoot? inst.root with
  | none => simp only [Option.any_none, Bool.false_eq_true, ↓reduceIte]; exact hS1
  | some root =>
  simp only [hI, hGR] at hA
  simp only [Option.any_some]
  by_cases hC : root.tables.contains (inst.slotFor tableId) = true
  · simp only [hC, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hA
    obtain ⟨hUse, hInR⟩ := hA
    have hR : st.objects[inst.root]? = some (.vspaceRoot root) :=
      (SystemState.getVSpaceRoot?_eq_some_iff st inst.root root).1 hGR
    have hNe : tableId ≠ inst.root := by intro h; rw [h, hR] at hT; cases hT
    let st1 := st.storePageTableWith tableId tableUninstalled
    have hO1 : st1.objects = st.objects.insert tableId (.pageTable (tableUninstalled table)) :=
      SystemState.storePageTableWith_objects hT tableUninstalled
    have hR1 : st1.objects[inst.root]? = some (.vspaceRoot root) := by
      rw [hO1, RHTable_getElem?_eq_get?, RHTable.get?_insert_ne_of_findsInPlace _ _ hInT hNe]
      exact hR
    have hInAfterTable : st1.objects.findsInPlace inst.root = true := by
      rw [hO1, RHTable.findsInPlace_insert_of_findsInPlace _ _ hInT]; exact hInR
    have hS2 := storeObject_root_slot_eq_inSlot hR1 hInAfterTable
      (fun r => r.withoutTableSlot inst tableId) rfl inst.level inst.index
      (fun r => [.invalidateAsid r.asid])
    simp only [hC, hUse, ↓reduceIte, Bool.false_eq_true]
    rw [hS1]
    dsimp only
    rw [show root.asid = (root.withoutTableSlot inst tableId).asid from rfl, hS2]
    rfl
  · simp only [hC, Bool.false_eq_true, ↓reduceIte]
    exact hS1

end SeLe4n.Kernel
