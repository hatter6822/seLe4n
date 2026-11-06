-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Delete
import SeLe4n.Kernel.MappingRecordStage.Capability
import SeLe4n.Kernel.ReschedulePendingArms.Dispatch

/-!
# The VSpace and page-table arms keep the records

WS-ZA ZA6.37.  The VSpace map, the unmap, the page-table install and removal
write VSpace roots, page tables, frames and one CNode: no thread.  A root store
may rebuild the ASID table, so these arms are `RecordsStage`s rather than
frames: the thread records are carried by the write touching roots alone
(`RecordsStage.of_vspaceRootOnlyWrite`), the teardown's well-formedness by the
root store keeping the root's ASID and adding no translation
(`teardownWellFormed_storeRoot`), and the map's new translation by its own
bundle theorem, whose 52-bit address bound the map's guard gives through
`physicalAddressWidthWithinBound`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A root stored over a root leaves the ASID table's own invariant. -/
theorem storeObject_vspaceRoot_asidTable_invExtK {st st' : SystemState} {rid : SeLe4n.ObjId}
    {r r' : VSpaceRoot} (hK : st.asidTable.invExtK) (hObj : st.objects[rid]? = some (.vspaceRoot r))
    (hS : storeObject rid (.vspaceRoot r') st = .ok ((), st')) : st'.asidTable.invExtK := by
  have hA : st'.asidTable = st.asidTable ∨
      st'.asidTable = (st.asidTable.erase r.asid).insert r'.asid rid := by
    unfold storeObject at hS; cases hS
    by_cases hk : storeKeepsAsid st rid (.vspaceRoot r') = true
    · exact Or.inl (if_pos hk)
    · simp only [hObj]; exact Or.inr (if_neg hk)
  rcases hA with e | e <;> rw [e]
  · exact hK
  · exact RobinHood.RHTable.insert_preserves_invExtK _ _ _
      (RobinHood.RHTable.erase_preserves_invExtK _ _ hK)

/-- **A root stored over a root, its ASID kept and no translation added, keeps
the state well formed.** -/
theorem teardownWellFormed_storeRoot {st st' : SystemState} {rid : SeLe4n.ObjId}
    {r r' : VSpaceRoot} (hT : teardownWellFormed st) (hObj : st.objects[rid]? = some (.vspaceRoot r))
    (hAsid : r'.asid = r.asid)
    (hSub : ∀ (v : SeLe4n.VAddr) (e : SeLe4n.PAddr × PagePermissions),
      r'.mappings[v]? = some e → r.mappings[v]? = some e)
    (hWF : r'.mappings.invExtK ∧ r'.mappingEpochs.invExtK)
    (hS : storeObject rid (.vspaceRoot r') st = .ok ((), st')) : teardownWellFormed st' := by
  obtain ⟨hB, hA⟩ := Architecture.storeObject_shrunkRoot_preserves_vspaceInvariantBundle st st' rid
    r r' hT.2.2 hT.1 hT.2.1 hObj hAsid hSub hWF hS
  exact ⟨storeObject_preserves_objects_invExt st st' _ _ hT.1 hS, hA, hB⟩

/-- A write of VSpace roots alone keeps every thread's reply view. -/
theorem replyViews_of_vspaceRootOnlyWrite {st st' : SystemState} (h : vspaceRootOnlyWrite st st') :
    st'.replyViews = st.replyViews := by
  funext k
  unfold SystemState.replyViews SystemState.getObject?
  rcases h k with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
  · rw [e]
  · rw [hr, hr']; rfl

namespace RecordsStage

/-- **A write of VSpace roots alone carries the records** once it keeps the
teardown's well-formedness and the machine's width. -/
theorem of_vspaceRootOnlyWrite {st st' : SystemState} (hR : vspaceRootOnlyWrite st st')
    (hT : st.kernelRecordsSound → teardownWellFormed st')
    (hW : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth) :
    RecordsStage st st' := fun h =>
  ⟨hT h, SystemState.replyWaitersConsistent.of_views (replyViews_of_vspaceRootOnlyWrite hR) h.2.1,
    (FaultsStayParked.of_vspaceRootOnlyWrite hR).preserves h.2.2.1, h.2.2.2.of_eq hW⟩

/-- **A root stored over a root**, its ASID kept and no translation added. -/
theorem storeRoot {st st' : SystemState} {rid : SeLe4n.ObjId} {r r' : VSpaceRoot}
    (hObj : st.objects[rid]? = some (.vspaceRoot r)) (hAsid : r'.asid = r.asid)
    (hSub : ∀ (v : SeLe4n.VAddr) (e : SeLe4n.PAddr × PagePermissions),
      r'.mappings[v]? = some e → r.mappings[v]? = some e)
    (hWF : r.mappings.invExtK ∧ r.mappingEpochs.invExtK →
      r'.mappings.invExtK ∧ r'.mappingEpochs.invExtK)
    (hS : storeObject rid (.vspaceRoot r') st = .ok ((), st')) : RecordsStage st st' := fun h =>
  have hI := KernelRecords.objects_invExt h
  of_vspaceRootOnlyWrite
    (fun oid => by
      by_cases hK : oid = rid
      · subst hK; exact Or.inr ⟨⟨r, hObj⟩, ⟨r', storeObject_objects_eq st st' _ _ hI hS⟩⟩
      · exact Or.inl (storeObject_objects_ne st st' rid oid _ hK hI hS))
    (fun h => teardownWellFormed_storeRoot h.1 hObj hAsid hSub
      (hWF (h.1.2.2.2.2.2.2.2.2.2 rid r hObj)) hS)
    (by rw [storeObject_machine_eq st st' _ _ hS]) h

/-- The physical-write ledger is no record. -/
theorem recordPhysicalWrites (st : SystemState) (ws : List Architecture.PhysicalWrite) :
    RecordsStage st (Architecture.recordPhysicalWrites st ws) := fun h =>
  (RecordsFrame.of_objects_eq (KernelRecords.objects_invExt h) rfl rfl).preserves h

end RecordsStage

/-! ### The arms -/

namespace RecordsStage

/-- **The page-table install**: the table, then the root gaining a table slot —
its ASID, translations and epochs kept. -/
theorem pageTableMap {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (h : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) : RecordsStage st st' := by
  obtain ⟨table, root, level, st1, hT, hR, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' h
  have hTo := (SystemState.getPageTable?_eq_some_iff _ _ _).1 hT
  have hRo := (SystemState.getVSpaceRoot?_eq_some_iff _ _ _).1 hR
  have hNe : rootId ≠ tableId := fun e => by subst e; rw [hTo] at hRo; cases hRo
  intro hK
  have hI := KernelRecords.objects_invExt hK
  have F1 := RecordsFrame.storeObject hI hS1 (by rw [hTo]; rfl) (fun _ => by simp)
  have hR1 : st1.objects[rootId]? = some (.vspaceRoot root) := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hI hS1]; exact hRo
  exact storeRoot (hS := hS2) (r := root) (by exact hR1) (by rfl) (fun _ _ h => by exact h)
    (fun w => by exact w) (recordPhysicalWrites st1 _ (F1.preserves hK))

/-- **The page-table removal**: the table's record cleared and, when its root
still holds it, the root losing the table slot. -/
theorem pageTableUnmap {tableId : SeLe4n.ObjId} {st st' : SystemState}
    (h : Architecture.pageTableUnmap tableId st = .ok ((), st')) : RecordsStage st st' := by
  intro hK
  have hI := KernelRecords.objects_invExt hK
  unfold Architecture.pageTableUnmap at h
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at h; cases h
  | some table =>
    have hTo := (SystemState.getPageTable?_eq_some_iff _ _ _).1 hT
    have Ft : ∀ {s : SystemState}, storeObject tableId (.pageTable table.uninstalled) st =
        .ok ((), s) → RecordsFrame st s :=
      fun hS => RecordsFrame.storeObject hI hS (by rw [hTo]; rfl) (fun _ => by simp)
    rw [hT] at h
    simp only at h
    split at h
    · cases h; exact hK
    · next inst _ =>
      split at h
      · exact (Ft h).preserves hK
      · next root hR =>
        have hRo := (SystemState.getVSpaceRoot?_eq_some_iff _ _ _).1 hR
        have hNe : inst.root ≠ tableId := fun e => by rw [e, hTo] at hRo; cases hRo
        split at h
        · split at h
          · cases h
          · cases hS1 : storeObject tableId (.pageTable table.uninstalled) st with
            | error e => rw [hS1] at h; cases h
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at h
              simp only at h
              have hR1 : st1.objects[inst.root]? = some (.vspaceRoot root) := by
                rw [storeObject_objects_ne _ _ _ _ _ hNe hI hS1]; exact hRo
              exact storeRoot (hS := h) (r := root) (by exact hR1) (by rfl)
                (fun _ _ h => by exact h) (fun w => by exact w)
                (recordPhysicalWrites st1 _ ((Ft hS1).preserves hK))
        · exact (Ft h).preserves hK

/-- **The unmap**: the root without the page, then the flush, the shootdown
round, the drain and the instruction-cache broadcast — none a record. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast {ec : Concurrency.CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : RecordsStage st st' := by
  intro hK
  obtain ⟨stU, hU, -⟩ := vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_objects ec asid vaddr
    st st' h
  obtain ⟨rid, r, r', hR, hU'⟩ : ∃ rid r r', Architecture.resolveAsidRoot st asid = some (rid, r) ∧
      r.unmapPage vaddr = some r' := by
    unfold Architecture.vspaceUnmapPage at hU
    cases hR : Architecture.resolveAsidRoot st asid with
    | none => rw [hR] at hU; cases hU
    | some p =>
      obtain ⟨rid, r⟩ := p
      rw [hR] at hU
      simp only at hU
      cases hU' : r.unmapPage vaddr with
      | none => rw [hU'] at hU; cases hU
      | some r' => exact ⟨rid, r, r', rfl, hU'⟩
  have hE := (vspaceUnmap_eq_unmapPageState ec asid vaddr st rid r r' hR hU').symm.trans h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hE
  have hF := vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec asid vaddr st st'
    (KernelRecords.objects_invExt hK) h
  exact of_vspaceRootOnlyWrite hF.2.1
    (fun hK => hE ▸ (unmapPageState_wellFormed (ec := ec) hK.1 hR hU').1)
    (by rw [vspaceUnmapPageWithShootdownAndIcacheBroadcast_machine_eq h]) hK

end RecordsStage

/-- The map's checked half, decomposed: the address guards passed against the
machine's width, the page-table write, then writes of the TLBs and the
shootdown state alone. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_tables
    (ec : Concurrency.CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore ec asid vaddr
      paddr perms st = .ok ((), st')) :
    vaddr.isCanonical = true ∧ paddr.toNat < 2 ^ st.machine.physicalAddressWidth ∧
      ∃ stB, Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), stB) ∧
        st'.objects = stB.objects ∧ st'.asidTable = stB.asidTable := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore at hStep
  cases hS : Architecture.vspaceMapPageCheckedWithShootdownFromState ec asid vaddr paddr
      perms st with
  | error e => rw [hS] at hStep; cases hStep
  | ok pr =>
    obtain ⟨u, stM⟩ := pr; cases u
    rw [hS] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    have hTail : st'.objects = stM.objects ∧ st'.asidTable = stM.asidTable := by
      subst hStep
      unfold Architecture.tlbFillOnCore Architecture.drainInitiatorPerCoreView
      split
      · exact ⟨rfl, rfl⟩
      · exact ⟨(Architecture.tlbInsertOnCore_frame _ _ _).1,
          (Architecture.tlbInsertOnCore_frame _ _ _).2.1⟩
    unfold Architecture.vspaceMapPageCheckedWithShootdownFromState at hS
    dsimp only at hS
    cases hF : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st with
    | error e => rw [hF] at hS; cases hS
    | ok pr2 =>
      obtain ⟨u2, stF⟩ := pr2; cases u2
      rw [hF] at hS
      simp only at hS
      have hRound : stM.objects = stF.objects ∧ stM.asidTable = stF.asidTable := by
        split at hS
        · rw [Architecture.withShootdownRound_total] at hS
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS
          exact ⟨rfl, rfl⟩
        · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS; exact ⟨rfl, rfl⟩
      unfold Architecture.vspaceMapPageCheckedWithFlushFromState at hF
      split at hF
      · cases hF
      · next hC =>
        split at hF
        · cases hF
        · next hB =>
          split at hF
          · cases hF
          · unfold Architecture.vspaceMapPageWithFlush at hF
            cases hM : Architecture.vspaceMapPage asid vaddr paddr perms st with
            | error e => rw [hM] at hF; cases hF
            | ok pr3 =>
              obtain ⟨u3, stB⟩ := pr3; cases u3
              rw [hM] at hF
              simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hF
              subst hF
              refine ⟨by simpa using hC, by simpa using hB, stB, rfl, ?_, ?_⟩
              · exact hTail.1.trans hRound.1
              · exact hTail.2.trans hRound.2

/-- **The page-table write keeps the state well formed** within the 52-bit
bound: its own bundle theorem, and the root stored over the root the ASID
resolved to. -/
theorem teardownWellFormed_vspaceMapPage {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions} {st st' : SystemState}
    (hT : teardownWellFormed st) (hBound : paddr.toNat < 2 ^ 52) (hCan : vaddr.isCanonical)
    (h : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    teardownWellFormed st' := by
  have hB := Architecture.vspaceMapPage_success_preserves_vspaceInvariantBundle st st' asid vaddr
    paddr perms hT.2.2 hBound hCan hT.1
    (fun _ root _ => (RobinHood.RHTable.erase_preserves_invExtK _ root.asid hT.2.1).1) hT.2.1
    (fun oid root hO => (hT.2.2.2.2.2.2.2.2.2 oid root hO).1.1) h
  refine ⟨(vspaceMapPage_ok_frame asid vaddr paddr perms st st' hT.1 h).1, ?_, hB⟩
  unfold Architecture.vspaceMapPage at h
  cases hRes : Architecture.resolveAsidRoot st asid with
  | none => rw [hRes] at h; cases h
  | some pr =>
    obtain ⟨rootId, root⟩ := pr
    rw [hRes] at h
    simp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hMp : root.mapPage vaddr paddr perms with
        | none => rw [hMp] at h; cases h
        | some root' =>
          rw [hMp] at h
          simp only at h
          obtain ⟨_, hObj, _⟩ := Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hRes
          exact storeObject_vspaceRoot_asidTable_invExtK (st := Architecture.recordPhysicalWrites st _)
            hT.2.1 hObj h

namespace RecordsStage

/-- **The map's checked half**: a root-only write within the machine's address
width. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore {ec : Concurrency.CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {paddr : SeLe4n.PAddr} {perms : PagePermissions}
    {st st' : SystemState}
    (h : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore ec asid vaddr paddr perms st
      = .ok ((), st')) : RecordsStage st st' := fun hK =>
  have hF := vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame ec asid vaddr paddr perms
    st st' (KernelRecords.objects_invExt hK) h
  of_vspaceRootOnlyWrite hF.2.1
    (fun hK => by
      obtain ⟨hC, hB, stB, hM, hO, hA⟩ :=
        vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_tables ec asid vaddr paddr perms st st' h
      exact teardownWellFormed_of_tables_eq hO hA
        (teardownWellFormed_vspaceMapPage hK.1 (hK.2.2.2.lt_bound hB) hC hM))
    (by rw [(vspaceMapPageCheckedWithShootdownFromStatePerCore_framed ec asid vaddr paddr perms st st'
      h).2]) hK

/-- **The frame's mapping tag**: the epoch written into the root, then the
frame's counter advanced. -/
theorem tagFrameMapping {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {frameId : SeLe4n.ObjId}
    {e : Nat} {st st' : SystemState} (h : _root_.SeLe4n.Kernel.tagFrameMapping asid vaddr frameId st
      = .ok (e, st')) : RecordsStage st st' := by
  obtain ⟨f, rootId, root, st1, hF, hR, -, h1, h2⟩ := tagFrameMapping_ok asid vaddr frameId st st' e h
  have hRootPre := (Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hR).2.1
  have hFramePre := (SystemState.getFrame?_eq_some_iff st frameId f).mp hF
  have hNe : frameId ≠ rootId := by intro hEq; rw [hEq, hRootPre] at hFramePre; cases hFramePre
  intro hK
  have hI := KernelRecords.objects_invExt hK
  have hK1 := storeRoot (hS := h1) (r := root) (by exact hRootPre) (by rfl)
    (fun _ _ h => by exact h)
    (fun w => by exact ⟨w.1, RobinHood.RHTable.insert_preserves_invExtK _ _ _ w.2⟩) hK
  have hF1 : st1.objects[frameId]? = some (.frame f) := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hI h1]; exact hFramePre
  exact (RecordsFrame.storeObject (KernelRecords.objects_invExt hK1) h2 (by rw [hF1]; rfl)
    (fun _ => by simp)).preserves hK1

/-- **The VSpace map**: the checked map, the tag, and the mapping recorded on
the capability that made it. -/
theorem vspaceMapFromFrameCap {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (h : _root_.SeLe4n.Kernel.vspaceMapFromFrameCap tid ec args st = .ok ((), st')) :
    RecordsStage st st' := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' h
  obtain ⟨cn, _, hC, -, hS⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  refine (vspaceMapPageCheckedWithShootdownFromStatePerCore hMap).trans
    ((tagFrameMapping hT).trans fun hK => ?_)
  exact (RecordsFrame.storeObject (KernelRecords.objects_invExt hK) hS
    (by rw [(SystemState.getCNode?_eq_some_iff _ _ _).1 hC]; rfl) (fun _ => by simp)).preserves hK

end RecordsStage

end SeLe4n.Kernel
