-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Architecture.VSpaceUnmapPerform

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

/-- WS-ZA ZA5.4: a fresh mapping cell, built out of line so that no caller's
equal literal is hoisted out of the branch that reuses a spare. -/
@[noinline] def mappingCellFresh (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) :
    Option (RobinHood.RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)) :=
  some ⟨vaddr, (paddr, perms), 0⟩

/-- WS-ZA ZA5.4: the value pair `(paddr, perms)` written over a spare pair `v`:
out of line, so `v` is the only cell the compiler can write it into, and its
address reads back through `v` so that `v` stays live, since an update of every
field would drop `v` and build a fresh pair (as `tlbEntryOverwrite`).  Equal to
the pair (`mappingValueOver_eq`). -/
@[noinline] def mappingValueOver (v : SeLe4n.PAddr × PagePermissions)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) : SeLe4n.PAddr × PagePermissions :=
  (if v.1.val = paddr.val then v.1 else paddr, perms)

theorem mappingValueOver_eq (v : SeLe4n.PAddr × PagePermissions)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) :
    mappingValueOver v paddr perms = (paddr, perms) := by
  unfold mappingValueOver
  split
  · rename_i h
    cases v with | mk a b => cases a; cases paddr; simp_all
  · rfl

/-- WS-ZA ZA5.4: the table entry of `vaddr ↦ (paddr, perms)` written over a spare
entry `e` and its value pair, out of line with its distance read back through
`e` (as `mappingValueOver`).  Equal to the entry (`mappingEntryOver_eq`). -/
@[noinline] def mappingEntryOver
    (e : RobinHood.RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions))
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions) :
    RobinHood.RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions) :=
  ⟨vaddr, mappingValueOver e.value paddr perms, if e.dist = 0 then e.dist else 0⟩

theorem mappingEntryOver_eq
    (e : RobinHood.RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions))
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions) :
    mappingEntryOver e vaddr paddr perms = ⟨vaddr, (paddr, perms), 0⟩ := by
  unfold mappingEntryOver
  rw [mappingValueOver_eq]
  split <;> simp_all

/-- WS-ZA ZA5.4: the mapping cell of `vaddr ↦ (paddr, perms)`, written over the
root's spare `o` (its `some`, its entry and its value pair) when it has one, out
of line so those are the cells the compiler writes into; with no spare it is
built (`mappingCellFresh`).  Equal to the fresh cell (`mappingCellOver_eq`). -/
@[noinline] def mappingCellOver
    (o : Option (RobinHood.RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)))
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions) :
    Option (RobinHood.RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)) :=
  match o with
  | some e => some (mappingEntryOver e vaddr paddr perms)
  | none => mappingCellFresh vaddr paddr perms

theorem mappingCellOver_eq
    (o : Option (RobinHood.RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)))
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions) :
    mappingCellOver o vaddr paddr perms = some ⟨vaddr, (paddr, perms), 0⟩ := by
  unfold mappingCellOver
  split
  · rw [mappingEntryOver_eq]
  · rfl

/-- WS-ZA ZA5.4: `rootWithMapping` as compiled: the root's spare cell is taken
out of its field before the insert, and the mapping written over it
(`mappingCellOver`) is the cell the table places (`RHTable.insertCell`), so a
map after an unmap builds no table entry. -/
@[inline] def rootWithMappingCells (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) (r : VSpaceRoot) : VSpaceRoot :=
  let sp := r.mappingSpare
  let r0 := { r with mappingSpare := Squash.mk none }
  Quot.lift
    (fun o => { r0 with mappings := r0.mappings.insertCell (mappingCellOver o vaddr paddr perms) })
    (fun a b _ => by dsimp only; rw [mappingCellOver_eq, mappingCellOver_eq]) sp

@[csimp] theorem rootWithMapping_eq_cells : @rootWithMapping = @rootWithMappingCells := by
  funext vaddr paddr perms r
  unfold rootWithMapping rootWithMappingCells
  cases r with
  | mk asid mappings tableBase tables mappingEpochs sp esp =>
    induction sp using Squash.ind with
    | h o =>
      simp only [Squash.mk]
      rw [mappingCellOver_eq, RobinHood.RHTable.insertCell_eq]
      simp only [VSpaceRoot.mk.injEq, and_true, true_and]
      exact Subsingleton.elim _ _

/-- WS-ZA ZA5.4: the root a mapping's epoch tag leaves (`tagFrameMapping`). -/
@[inline] def rootWithEpoch (vaddr : SeLe4n.VAddr) (epoch : Nat) (r : VSpaceRoot) :
    VSpaceRoot :=
  { r with mappingEpochs := r.mappingEpochs.insert vaddr epoch }

/-- WS-ZA ZA5.4: a fresh epoch cell, built out of line (as `mappingCellFresh`)
so that its literal is not merged with the arm that reuses a spare. -/
@[noinline] def epochCellFresh (vaddr : SeLe4n.VAddr) (epoch : Nat) :
    Option (RobinHood.RHEntry SeLe4n.VAddr Nat) :=
  some ⟨vaddr, epoch, 0⟩

/-- WS-ZA ZA5.4: the table entry of `vaddr ↦ epoch` written over a spare entry
`e`, out of line with its distance read back through `e` (as
`mappingEntryOver`).  Equal to the entry (`epochEntryOver_eq`). -/
@[noinline] def epochEntryOver (e : RobinHood.RHEntry SeLe4n.VAddr Nat)
    (vaddr : SeLe4n.VAddr) (epoch : Nat) : RobinHood.RHEntry SeLe4n.VAddr Nat :=
  ⟨vaddr, epoch, if e.dist = 0 then e.dist else 0⟩

theorem epochEntryOver_eq (e : RobinHood.RHEntry SeLe4n.VAddr Nat)
    (vaddr : SeLe4n.VAddr) (epoch : Nat) : epochEntryOver e vaddr epoch = ⟨vaddr, epoch, 0⟩ := by
  unfold epochEntryOver
  split <;> simp_all

/-- WS-ZA ZA5.4: the epoch cell of `vaddr ↦ epoch`, written over the root's
spare epoch cell `o` (its `some` and its entry) when it has one, out of line so
those are the cells the compiler writes into; with no spare it is built
(`epochCellFresh`).  Equal to the fresh cell (`epochCellOver_eq`). -/
@[noinline] def epochCellOver (o : Option (RobinHood.RHEntry SeLe4n.VAddr Nat))
    (vaddr : SeLe4n.VAddr) (epoch : Nat) : Option (RobinHood.RHEntry SeLe4n.VAddr Nat) :=
  match o with
  | some e => some (epochEntryOver e vaddr epoch)
  | none => epochCellFresh vaddr epoch

theorem epochCellOver_eq (o : Option (RobinHood.RHEntry SeLe4n.VAddr Nat))
    (vaddr : SeLe4n.VAddr) (epoch : Nat) : epochCellOver o vaddr epoch = some ⟨vaddr, epoch, 0⟩ := by
  unfold epochCellOver
  split
  · rw [epochEntryOver_eq]
  · rfl

/-- WS-ZA ZA5.4: `rootWithEpoch` as compiled: the root's spare epoch cell, which
the unmap before it left (`rootWithoutEpochCells`), taken out of its field and
written over (`epochCellOver`) as the cell the table places, so a map after an
unmap builds no epoch entry, whatever address it maps. -/
@[inline] def rootWithEpochCells (vaddr : SeLe4n.VAddr) (epoch : Nat) (r : VSpaceRoot) :
    VSpaceRoot :=
  let sp := r.epochSpare
  let r0 := { r with epochSpare := Squash.mk none }
  Quot.lift
    (fun o => { r0 with mappingEpochs := r0.mappingEpochs.insertCell (epochCellOver o vaddr epoch) })
    (fun a b _ => by dsimp only; rw [epochCellOver_eq, epochCellOver_eq]) sp

@[csimp] theorem rootWithEpoch_eq_cells : @rootWithEpoch = @rootWithEpochCells := by
  funext vaddr epoch r
  unfold rootWithEpoch rootWithEpochCells
  cases r with
  | mk asid mappings tableBase tables mappingEpochs sp esp =>
    induction esp using Squash.ind with
    | h o =>
      simp only [Squash.mk]
      rw [epochCellOver_eq, RobinHood.RHTable.insertCell_eq]
      simp only [VSpaceRoot.mk.injEq, and_true, true_and]
      exact Subsingleton.elim _ _

/-- WS-ZA ZA5.4: the frame a mapping's epoch tag leaves: its counter advanced. -/
@[inline] def frameWithNextEpoch (f : FrameObject) : FrameObject :=
  { f with mapEpoch := f.mapEpoch + 1 }

/-- WS-ZA ZA5.4: the frame's map epoch, read as a word. -/
@[inline] def frameMapEpochOf (st : SystemState) (frameId : SeLe4n.ObjId) : Nat :=
  match st.getFrame? frameId with
  | some f => f.mapEpoch
  | none => 0

/-- WS-ZA ZA5.4: the capability's mapping record written in its CNode slot —
`cspaceRecordFrameMappingImpl`'s write, total: the record's words go into the
slot's own capability (`CNode.recordMappingCells`). -/
@[inline] def recordFrameMappingAt (st : SystemState) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (m : FrameMapping) : SystemState :=
  match st.getCNode? cnode with
  | some cn =>
    match cn.lookup slot with
    | some _ => st.storeCNodeWith cnode (·.recordMappingCells slot m.asid m.vaddr m.epoch)
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
    (Architecture.drainInitiatorPageOnCore st2 ec asid vaddr) ec asid vaddr

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
@[inline] def vspaceMapAdmittedAt (st : SystemState) (args : VSpaceMapArgs) (frameCap : Capability)
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

/-- WS-ZA ZA5.4: a slot record written over a spare one `s`: out of line, with
its level read back through `s` so that `s` stays live and is the cell written
(as `mappingValueOver`).  Equal to the slot (`slotOver_eq`). -/
@[noinline] def slotOver (s : PageTableSlot) (level index : Nat) (table : SeLe4n.ObjId) :
    PageTableSlot :=
  ⟨if s.level = level then s.level else level, index, table⟩

theorem slotOver_eq (s : PageTableSlot) (level index : Nat) (table : SeLe4n.ObjId) :
    slotOver s level index table = ⟨level, index, table⟩ := by
  unfold slotOver
  split <;> simp_all

/-- WS-ZA ZA5.4: a fresh slot cell, built out of line so that its literal is not
merged with the arm that reuses a spare (as `mappingCellFresh`). -/
@[noinline] def slotCellFresh (level index : Nat) (table : SeLe4n.ObjId) : List PageTableSlot :=
  [⟨level, index, table⟩]

/-- WS-ZA ZA5.4: the one-slot list a table install appends to its root, written
over the table's spare cell `c` (its list cell and its slot record) when it has
one; with none it is built (`slotCellFresh`).  Equal to the fresh cell
(`slotCellOver_eq`). -/
@[noinline] def slotCellOver (c : List PageTableSlot) (level index : Nat) (table : SeLe4n.ObjId) :
    List PageTableSlot :=
  match c with
  | s :: _ => slotOver s level index table :: []
  | [] => slotCellFresh level index table

theorem slotCellOver_eq (c : List PageTableSlot) (level index : Nat) (table : SeLe4n.ObjId) :
    slotCellOver c level index table = [⟨level, index, table⟩] := by
  unfold slotCellOver
  split
  · rw [slotOver_eq]
  · rfl

/-- WS-ZA ZA5.4: the table's record once installed, its spare slot cell handed
to the root (`PageTableObject.with_slotCell`). -/
@[inline] def tableInstalledHanding (rootId : SeLe4n.ObjId) (level index : Nat)
    (t : PageTableObject) : PageTableObject :=
  { t.installedAt rootId level index with slotCell := Squash.mk [] }

/-- WS-ZA ZA5.4: the root once it holds `table` at `(level, index)`, the slot
written over the table's cell `cell` (`slotCellOver`). -/
@[inline] def rootWithTableCell (cell : TableSlotCell) (level index : Nat)
    (table : SeLe4n.ObjId) (r : VSpaceRoot) : VSpaceRoot :=
  Quot.lift (fun c => { r with tables := r.tables ++ slotCellOver c level index table })
    (fun a b _ => by dsimp only; rw [slotCellOver_eq, slotCellOver_eq]) cell

/-- WS-ZA ZA5.4: the spare slot cell of the table at `tableId`, read before the
table's store releases it. -/
@[inline] def tableSlotCellOf (st : SystemState) (tableId : SeLe4n.ObjId) : TableSlotCell :=
  match st.getPageTable? tableId with
  | some t => t.slotCell
  | none => Squash.mk []

/-- WS-ZA ZA5.4: `pageTableMapPerformAt` as compiled: the table's spare slot
cell is read, the table's store releases it, and the root's slot is written over
it, so an install builds no slot (`pageTableMapPerformAt_eq_cells`). -/
def pageTableMapPerformCells (tableId rootId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr)
    (st : SystemState) : SystemState :=
  let level := pageTableMapLevelAt st rootId vaddr
  let index := PageTableSlot.indexOf level vaddr
  let cell := tableSlotCellOf st tableId
  let st1 := st.storePageTableWith tableId (tableInstalledHanding rootId level index)
  let st2 := st1.storeVSpaceRootWith rootId (rootWithTableCell cell level index tableId)
  Architecture.recordPhysicalWrites st2 (rootSlotLedger st2 rootId level index)

@[csimp] theorem pageTableMapPerformAt_eq_cells :
    @pageTableMapPerformAt = @pageTableMapPerformCells := by
  funext tableId rootId vaddr st
  unfold pageTableMapPerformAt pageTableMapPerformCells
  have hT : ∀ rootId level index,
      tableInstalledHanding rootId level index = (·.installedAt rootId level index) := by
    intro rootId level index; funext t
    simp only [tableInstalledHanding, PageTableObject.with_slotCell]
  have hR : ∀ (cell : TableSlotCell) level index (table : SeLe4n.ObjId),
      rootWithTableCell cell level index table = (·.withTableSlot level index table) := by
    intro cell level index table; funext r
    induction cell using Squash.ind with
    | h c =>
      simp only [rootWithTableCell, Squash.mk, slotCellOver_eq]
      rfl
  simp only [hT, hR]

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
  t.uninstalled

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
         !VSpaceRoot.slotHeldIn inst.level inst.index tableId root.tables ||
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
  have hS1 : storeObject tableId (.pageTable table.uninstalled) st =
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
  simp only [hI, hGR, VSpaceRoot.slotHeldIn_eq] at hA
  simp only [Option.any_some, PageTableInstall.slotFor]
  by_cases hC : root.tables.contains
      { level := inst.level, index := inst.index, table := tableId } = true
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

/-- WS-ZA ZA5.4: whether a root slot is kept by the removal of the table
`table` from `(level, index)` (`VSpaceRoot.withoutTableSlot`).  Out of line, so
the walk branches once on its answer: inlined, its two failing tests joined at
one point, where the kept slot's list cell was built fresh rather than reused. -/
@[noinline] def keepsTableSlot (level index : Nat) (table : SeLe4n.ObjId) (s : PageTableSlot) :
    Bool :=
  !(s.level == level && s.index == index && s.table == table)

/-- WS-ZA ZA5.4: the walk of a root's slots `ts` for the one a table removal
takes out, the slots before it kept in `acc` (reversed): their cells are
reused, the removed slot's list cell and record become the root's slot cell in
transit (`VSpaceRoot.tableSlotSpare`), and the slots after it are filtered as
the specification does.  The root's other fields are `r0`'s.  Equal to the
filter (`rootWithoutTableCellLoop_eq`). -/
def rootWithoutTableCellLoop (level index : Nat) (table : SeLe4n.ObjId) (r0 : VSpaceRoot) :
    List PageTableSlot → List PageTableSlot → VSpaceRoot
  | acc, [] => { r0 with tables := acc.reverse }
  | acc, s :: tl =>
    if keepsTableSlot level index table s then
      rootWithoutTableCellLoop level index table r0 (s :: acc) tl
    else
      { r0 with
          tables := List.reverseAux acc (tl.filter (keepsTableSlot level index table))
          tableSlotSpare := Squash.mk (s :: []) }

theorem rootWithoutTableCellLoop_eq (level index : Nat) (table : SeLe4n.ObjId) (r0 : VSpaceRoot)
    (acc ts : List PageTableSlot) :
    rootWithoutTableCellLoop level index table r0 acc ts =
      { r0 with tables := acc.reverse ++ ts.filter (keepsTableSlot level index table) } := by
  induction ts generalizing acc with
  | nil => simp [rootWithoutTableCellLoop]
  | cons s tl ih =>
    unfold rootWithoutTableCellLoop
    split
    · next h => rw [ih, List.filter_cons_of_pos h]; simp
    · next h =>
      rw [List.filter_cons_of_neg h, List.reverseAux_eq]
      cases r0
      simp only [VSpaceRoot.mk.injEq, true_and]
      exact Subsingleton.elim _ _

/-- WS-ZA ZA5.4: the root once the slot `(level, index)` for `table` is removed,
the removed slot's cell kept in transit (`rootWithoutTableCellLoop`).  Out of
line, so the root arrives exclusive.  Equal to the removal
(`rootWithoutTableCell_eq`). -/
@[noinline] def rootWithoutTableCell (level index : Nat) (table : SeLe4n.ObjId) (r : VSpaceRoot) :
    VSpaceRoot :=
  rootWithoutTableCellLoop level index table { r with tables := [] } [] r.tables

theorem rootWithoutTableCell_eq (root : SeLe4n.ObjId) (level index : Nat) (table : SeLe4n.ObjId) :
    rootWithoutTableCell level index table = (·.withoutTableSlot ⟨root, level, index⟩ table) := by
  funext r
  unfold rootWithoutTableCell
  rw [rootWithoutTableCellLoop_eq]
  rfl

/-- WS-ZA ZA5.4: **the hand-over of a removed table's slot cell from the root to
the table** — the identity, since neither field is anything a theorem reads
(`VSpaceRoot.with_tableSlotSpare`, `PageTableObject.with_slotCell`).  Compiled
(`handTableSlotCell_eq_impl`), the cell is read from the root, the root's field
is cleared and the table's is set, each in its object's slot, so the table holds
the cell alone. -/
def handTableSlotCell (st : SystemState) (_rootId _tableId : SeLe4n.ObjId) : SystemState := st

/-- WS-ZA ZA5.4: the slot cell a root holds in transit. -/
@[inline] def rootSlotSpareOf (st : SystemState) (rootId : SeLe4n.ObjId) : TableSlotCell :=
  match st.getVSpaceRoot? rootId with
  | some r => r.tableSlotSpare
  | none => Squash.mk []

/-- WS-ZA ZA5.4: the compiled `handTableSlotCell`. -/
def handTableSlotCellImpl (st : SystemState) (rootId tableId : SeLe4n.ObjId) : SystemState :=
  let cell := rootSlotSpareOf st rootId
  let clear := SystemState.mapVSpaceRootObject (fun r => { r with tableSlotSpare := Squash.mk [] })
  let st1 := st.modifyObjectInPlace rootId clear
  let give := SystemState.mapPageTableObject (fun t => { t with slotCell := cell })
  st1.modifyObjectInPlace tableId give

@[csimp] theorem handTableSlotCell_eq_impl : @handTableSlotCell = @handTableSlotCellImpl := by
  funext st rootId tableId
  unfold handTableSlotCell handTableSlotCellImpl
  dsimp only
  rw [SystemState.modifyObjectInPlace_of_id _ _ _ (by
      intro o; cases o <;> simp [SystemState.mapVSpaceRootObject] <;> rfl),
    SystemState.modifyObjectInPlace_of_id _ _ _ (by
      intro o; cases o <;> simp [SystemState.mapPageTableObject] <;> rfl)]

/-- WS-ZA ZA5.4: the removal's two ledger records for the slot
`(rootId, level, index)`, the parent entry's store and the ASID invalidate, each
recorded on its own and read as words, so neither the list of them nor the slot
record is built (`recordDetachedSlotAt_eq`). -/
@[inline] def recordDetachedSlotAt (st : SystemState) (rootId : SeLe4n.ObjId) (level index : Nat) :
    SystemState :=
  match st.getVSpaceRoot? rootId with
  | some r =>
    Architecture.recordPhysicalWrites
      (Architecture.recordPhysicalWrites st (Architecture.slotStore? st r level index).toList)
      [.invalidateAsid r.asid]
  | none => st

/-- WS-ZA ZA5.4: `pageTableUnmapPerformAt` as compiled: the install read as
words under its flag, the removed slot's cell handed back to the table
(`rootWithoutTableCell`, `handTableSlotCell`), and the ledger written record by
record (`recordDetachedSlotAt`), so a removal builds nothing
(`pageTableUnmapPerformAt_eq_cells`). -/
def pageTableUnmapPerformCells (tableId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  match st.getPageTable? tableId with
  | some table =>
    if table.installed then
      let rootId := table.installRoot
      let level := table.installLevel
      let index := table.installIndex
      let live := Architecture.pageTableInstallLive st tableId
      let st1 := st.storePageTableWith tableId tableUninstalled
      if live then
        let st2 := st1.storeVSpaceRootWith rootId (rootWithoutTableCell level index tableId)
        recordDetachedSlotAt (handTableSlotCell st2 rootId tableId) rootId level index
      else st1
    else st
  | none => st

theorem recordDetachedSlotAt_eq (st : SystemState) (rootId : SeLe4n.ObjId) (level index : Nat) :
    recordDetachedSlotAt st rootId level index =
      Architecture.recordPhysicalWrites st (detachedSlotLedger st ⟨rootId, level, index⟩) := by
  unfold recordDetachedSlotAt detachedSlotLedger
  dsimp only
  split
  · rw [Architecture.recordPhysicalWrites_append]
  · rfl

@[csimp] theorem pageTableUnmapPerformAt_eq_cells :
    @pageTableUnmapPerformAt = @pageTableUnmapPerformCells := by
  funext tableId st
  unfold pageTableUnmapPerformAt pageTableUnmapPerformCells
  split
  · next table _ =>
    unfold PageTableObject.installedIn
    cases table.installed
    · rfl
    · simp only [↓reduceIte, rootWithoutTableCell_eq table.installRoot, handTableSlotCell,
        recordDetachedSlotAt_eq]
  · rfl

end SeLe4n.Kernel
