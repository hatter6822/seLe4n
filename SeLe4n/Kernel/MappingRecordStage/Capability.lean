-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Basic
import SeLe4n.Kernel.Capability.Invariant.Preservation.SetSpaceMappingRecords
import SeLe4n.Kernel.Capability.Invariant.Preservation.Bookkeeping
import SeLe4n.Kernel.KernelRecords.Frame

/-! # The capability and VSpace arms keep the mappings recorded

The copy, mint, move and reply-cap mint, the reset, the VSpace map, unmap and
instruction-page unify, the page-table install and removal, the finalising
revocation, the zombie delete and the thread-space set are proven to keep the
mappings recorded at the operation (`Kernel/MappingRecordPreservation.lean`,
`Capability/Invariant/Preservation/{MappingRecords,SetSpaceMappingRecords}.lean`).
Here each is a `MappingStage`.

The map, the unmap, the deletes and the space set read two facts besides the
store's table invariant: the capability invariants and the teardown's
well-formedness (`MappingArmPremises`).  An entry reads them off the state it
starts from and carries them across the register writes it makes before the
arm (`MappingArmPremises.updateTcb`, `MappingArmPremises.of_tables_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)

/-- **What the delete-chain, set-space and VSpace arms read besides**: the
capability invariants and the teardown's well-formedness. -/
structure MappingArmPremises (st : SystemState) : Prop where
  caps : capabilityInvariantBundle st
  teardown : teardownWellFormed st

namespace MappingArmPremises

variable {st st' : SystemState}

theorem objInv (P : MappingArmPremises st) : st.objects.invExt :=
  objects_invExt_of_capabilityInvariantBundle st P.caps

/-- A state with the same objects, derivation tree and ASID table. -/
theorem of_tables_eq (P : MappingArmPremises st) (hO : st'.objects = st.objects)
    (hC : st'.cdt = st.cdt) (hA : st'.asidTable = st.asidTable) : MappingArmPremises st' :=
  ⟨capabilityInvariantBundle_of_objects_and_cdt_eq P.caps hO hC,
    teardownWellFormed_of_tables_eq hO hA P.teardown⟩

/-- One thread's record rewritten, its space slots kept: a register write. -/
theorem updateTcb (P : MappingArmPremises st) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ t, (f t).spaceCells = t.spaceCells ∧ (f t).spaceLinks = t.spaceLinks ∧
      (f t).boundNotificationCode = t.boundNotificationCode := by
      intro _; exact ⟨rfl, rfl, rfl⟩)
    (hW : ∀ t, (f t).taintWords = t.taintWords := by taint_words_kept) :
    MappingArmPremises (st.updateTcb tid f) := by
  have hI := P.objInv
  have hI' := SystemState.updateTcb_preserves_objects_invExt st tid f hI
  refine ⟨capabilityInvariantBundle_of_kindPreserving P.caps (SystemState.updateTcb_cdt _ _ _) hI'
    (SystemState.updateTcb_kindPreservingWrite st tid f hI hf hW), ?_⟩
  refine teardownWellFormed_of_roots_eq hI' (SystemState.updateTcb_asidTable _ _ _)
    (fun oid r => ?_) P.teardown
  by_cases hk : tid.toObjId = oid
  · subst hk
    cases hT : st.getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]
    | some t =>
      rw [SystemState.updateTcb_eq_of_some hT, (SystemState.getTcb?_eq_some_iff st tid t).mp hT]
      simp only [RHTable_getElem?_eq_get?]
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hI]
      constructor <;> intro e <;> cases e
  · rw [SystemState.updateTcb_objects_ne _ _ _ _ hk hI]

/-- **The premises from the kernel's invariants**: the capability invariants are
a `proofLayerInvariantBundle` conjunct, and the teardown's well-formedness is the
first of the records every kernel entry carries (`kernelRecordsSound`, which the
started boot installs and every entry keeps). -/
theorem of_kernelRecordsSound (hB : Architecture.proofLayerInvariantBundle st)
    (hR : st.kernelRecordsSound) : MappingArmPremises st :=
  ⟨hB.2.1, hR.1⟩

end MappingArmPremises

/-! ### The slot-writing arms -/

theorem cspaceCopy_mappingStage {src dst : CSpaceAddr} {st st' : SystemState}
    (hC : capabilityInvariantBundle st) (h : cspaceCopy src dst st = .ok ((), st')) :
    MappingStage st st' :=
  MappingStage.of_preserves (fun _ => objects_invExt_of_capabilityInvariantBundle _
      (cspaceCopy_preserves_capabilityInvariantBundle st st' src dst hC h))
    (fun hI hL => cspaceCopy_preserves_liveMappingsRecorded hI hL h)
    fun hI hB => cspaceCopy_preserves_bookkeepingAgrees hI hB h

theorem cspaceMintWithCdt_mappingStage {src dst : CSpaceAddr} {rights : AccessRightSet}
    {badge : Option SeLe4n.Badge} {st st' : SystemState} (hC : capabilityInvariantBundle st)
    (h : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) : MappingStage st st' :=
  MappingStage.of_preserves (fun _ => objects_invExt_of_capabilityInvariantBundle _
      (cspaceMintWithCdt_preserves_capabilityInvariantBundle st st' src dst rights badge hC h))
    (fun hI hL => cspaceMintWithCdt_preserves_liveMappingsRecorded hI hL h)
    fun hI hB => cspaceMintWithCdt_preserves_bookkeepingAgrees hI hB h

theorem cspaceMove_mappingStage {src dst : CSpaceAddr} {st st' : SystemState}
    (hC : capabilityInvariantBundle st) (h : cspaceMove src dst st = .ok ((), st')) :
    MappingStage st st' :=
  MappingStage.of_preserves (fun _ => objects_invExt_of_capabilityInvariantBundle _
      (cspaceMove_preserves_capabilityInvariantBundle st st' src dst hC h))
    (fun hI hL => cspaceMove_preserves_liveMappingsRecorded hI hL h)
    fun hI hB => cspaceMove_preserves_bookkeepingAgrees hI hB h

theorem mintReplyCapWithCdt_mappingStage {src dst : CSpaceAddr} {st st' : SystemState}
    (hC : capabilityInvariantBundle st) (h : mintReplyCapWithCdt src dst st = .ok ((), st')) :
    MappingStage st st' :=
  MappingStage.of_preserves (fun _ => objects_invExt_of_capabilityInvariantBundle _
      (mintReplyCapWithCdt_preserves_capabilityInvariantBundle st st' src dst hC h))
    (fun hI hL => mintReplyCapWithCdt_preserves_liveMappingsRecorded hI hL h)
    fun hI hB => mintReplyCapWithCdt_preserves_bookkeepingAgrees hI hB h

/-- The reset writes the invoked capability's free index alone. -/
theorem untypedResetFromCap_mappingStage {tid : SeLe4n.ThreadId} {srcAddr : SeLe4n.CPtr}
    {st st' : SystemState} (h : untypedResetFromCap tid srcAddr st = .ok ((), st')) :
    MappingStage st st' := by
  obtain ⟨_, _, _, _, _, hR⟩ := untypedResetFromCap_ok tid srcAddr st st' h
  refine MappingStage.of_preserves (fun hI => ?_)
    (fun hI hL => untypedResetFromCap_preserves_liveMappingsRecorded tid srcAddr hI hL h)
    fun hI hB => ?_
  · rw [untypedResetSlot_ok_frame hR]; exact setCapFreeIndex_preserves_objects_invExt hI
  · rw [untypedResetSlot_ok_frame hR]; exact setCapFreeIndex_preserves_bookkeepingAgrees hI hB

/-! ### The VSpace and page-table arms -/

/-- The map writes the root, tags the frame and the root's epoch, and records
the mapping on the capability that made it: each a store. -/
theorem vspaceMapFromFrameCap_objects_invExt {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (hI : st.objects.invExt) (h : vspaceMapFromFrameCap tid ec args st = .ok ((), st')) :
    st'.objects.invExt := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' h
  have hI1 := (vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ st st1 hI
    hMap).1
  obtain ⟨_, _, _, st3, -, -, -, h1, h2⟩ := tagFrameMapping_ok _ _ _ st1 st2 epoch hT
  have hI2 := storeObject_preserves_objects_invExt _ _ _ _
    (storeObject_preserves_objects_invExt _ _ _ _ hI1 h1) h2
  obtain ⟨_, _, -, -, hS⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  exact storeObject_preserves_objects_invExt _ _ _ _ hI2 hS

/-- The map writes the root through a store, then TLB, shootdown and fill state
alone: no ghost moves after the store. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_ghosts
    (ec : Concurrency.CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore ec asid vaddr
      paddr perms st = .ok ((), st')) :
    ∃ stB, Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), stB) ∧
      SystemState.ghostsKept st' stB := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore at hStep
  cases hS : Architecture.vspaceMapPageCheckedWithShootdownFromState ec asid vaddr paddr
      perms st with
  | error e => rw [hS] at hStep; cases hStep
  | ok pr =>
    obtain ⟨u, stM⟩ := pr; cases u
    rw [hS] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    have hTail : SystemState.ghostsKept st' stM := by
      subst hStep
      unfold Architecture.tlbFillOnCore Architecture.drainInitiatorPerCoreView
      split
      · exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
      · unfold Architecture.tlbInsertOnCore
        split <;> exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
    unfold Architecture.vspaceMapPageCheckedWithShootdownFromState at hS
    dsimp only at hS
    cases hF : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st with
    | error e => rw [hF] at hS; cases hS
    | ok pr2 =>
      obtain ⟨u2, stF⟩ := pr2; cases u2
      rw [hF] at hS
      simp only at hS
      have hRound : SystemState.ghostsKept stM stF := by
        split at hS
        · rw [Architecture.withShootdownRound_total] at hS
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS
          exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
        · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
          subst hS; exact .refl _
      unfold Architecture.vspaceMapPageCheckedWithFlushFromState at hF
      split at hF
      · cases hF
      · split at hF
        · cases hF
        · split at hF
          · cases hF
          · unfold Architecture.vspaceMapPageWithFlush at hF
            cases hB : Architecture.vspaceMapPage asid vaddr paddr perms st with
            | error e => rw [hB] at hF; cases hF
            | ok pr3 =>
              obtain ⟨u3, stB⟩ := pr3; cases u3
              rw [hB] at hF
              simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hF
              subst hF
              exact ⟨stB, rfl, hTail.trans (hRound.trans ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩)⟩

/-- The page-table write the map makes is a store. -/
theorem vspaceMapPage_preserves_bookkeepingAgrees {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    st'.bookkeepingAgrees := by
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
          exact storeObject_preserves_bookkeepingAgrees (Architecture.recordPhysicalWrites st _) _
            _ _ (hB.of_objects_ghosts rfl ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩) hObjInv h

/-- **The map keeps the agreement**: the root's store, the frame's and the
root's epoch stores, and the record on the capability are each a store. -/
theorem vspaceMapFromFrameCap_preserves_bookkeepingAgrees {tid : SeLe4n.ThreadId}
    {ec : Concurrency.CoreId} {args : Architecture.SyscallArgDecode.VSpaceMapArgs}
    {st st' : SystemState} (hI : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : vspaceMapFromFrameCap tid ec args st = .ok ((), st')) : st'.bookkeepingAgrees := by
  obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid ec args st st' h
  have hI1 := (vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ st st1 hI
    hMap).1
  obtain ⟨stB, hMB, hG⟩ := vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_ghosts _ _ _ _ _
    st st1 hMap
  obtain ⟨stB', hMB', hO⟩ := vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_objects _ _ _ _ _
    st st1 hMap
  rw [hMB] at hMB'
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hMB'
  subst hMB'
  have hB1 := (vspaceMapPage_preserves_bookkeepingAgrees hI hB hMB).of_objects_ghosts hO hG
  obtain ⟨_, _, _, st3, -, -, -, h1, h2⟩ := tagFrameMapping_ok _ _ _ st1 st2 epoch hT
  have hI3 := storeObject_preserves_objects_invExt _ _ _ _ hI1 h1
  have hB2 := storeObject_preserves_bookkeepingAgrees _ _ _ _
    (storeObject_preserves_bookkeepingAgrees _ _ _ _ hB1 hI1 h1) hI3 h2
  obtain ⟨_, _, -, -, hS⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  exact storeObject_preserves_bookkeepingAgrees _ _ _ _ hB2
    (storeObject_preserves_objects_invExt _ _ _ _ hI3 h2) hS

/-- **The unmap keeps the agreement**: it writes the root as a root
(`unmapPageState`), and no ghost. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_bookkeepingAgrees
    {ec : Concurrency.CoreId} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (hI : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : st'.bookkeepingAgrees := by
  obtain ⟨-, hW, -⟩ := vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec asid vaddr st st'
    hI h
  obtain ⟨-, -, -, -, -, e⟩ := vspaceUnmap_ok_unmapPageState h
  exact hB.of_vspaceRootOnlyWrite hW (e ▸ unmapPageState_ghostsKept ec asid vaddr st)

theorem vspaceMapFromFrameCap_mappingStage {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId}
    {args : Architecture.SyscallArgDecode.VSpaceMapArgs} {st st' : SystemState}
    (hW : teardownWellFormed st) (h : vspaceMapFromFrameCap tid ec args st = .ok ((), st')) :
    MappingStage st st' :=
  MappingStage.of_preserves (fun hI => vspaceMapFromFrameCap_objects_invExt hI h)
    (fun _ hL => vspaceMapFromFrameCap_preserves_liveMappingsRecorded tid ec args st st' hW hL h)
    fun hI hB => vspaceMapFromFrameCap_preserves_bookkeepingAgrees hI hB h

theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_mappingStage {ec : Concurrency.CoreId}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {st st' : SystemState}
    (hW : teardownWellFormed st)
    (h : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) : MappingStage st st' :=
  MappingStage.of_preserves
    (fun hI => (vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame ec asid vaddr st st' hI h).1)
    (fun _ hL => vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_liveMappingsRecorded
      ec asid vaddr st st' hW hL h)
    fun hI hB => vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_bookkeepingAgrees hI hB h

/-- **The live `.vspaceMap` arm, map or remap, keeps the mappings recorded**: a
remap is the unmap of the address the frame capability records, which keeps the
state well formed, followed by a fresh mapping from the state it leaves. -/
theorem vspaceMapOrRemapFromFrameCap_mappingStage {tid : SeLe4n.ThreadId}
    {ec : Concurrency.CoreId} {args : Architecture.SyscallArgDecode.VSpaceMapArgs}
    {st st' : SystemState} (hW : teardownWellFormed st)
    (h : vspaceMapOrRemapFromFrameCap tid ec args st = .ok ((), st')) :
    MappingStage st st' := by
  rcases vspaceMapOrRemapFromFrameCap_cases h with hM | ⟨st0, hU, hM⟩
  · exact vspaceMapFromFrameCap_mappingStage hW hM
  · exact (vspaceUnmapPageWithShootdownAndIcacheBroadcast_mappingStage hW hU).trans
      (vspaceMapFromFrameCap_mappingStage (vspaceUnmap_preserves_teardownWellFormed hW hU) hM)

theorem vspaceUnifyInstructionPage_mappingStage {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (h : Architecture.vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    MappingStage st st' :=
  MappingStage.of_objects_eq (Architecture.vspaceUnifyInstructionPage_frame h).1
    (Architecture.vspaceUnifyInstructionPage_ghostsKept h)

/-- The page-table install stores the table, then the root. -/
theorem pageTableMap_objects_invExt {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (hI : st.objects.invExt)
    (h : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    st'.objects.invExt := by
  obtain ⟨_, _, _, st1, -, -, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' h
  have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hI hS1
  exact storeObject_preserves_objects_invExt _ _ _ _
    (by rw [Architecture.recordPhysicalWrites_objects]; exact hI1) hS2

/-- The page-table removal stores the table and, when its root still holds it,
the root. -/
theorem pageTableUnmap_objects_invExt {tableId : SeLe4n.ObjId} {st st' : SystemState}
    (hI : st.objects.invExt) (h : Architecture.pageTableUnmap tableId st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold Architecture.pageTableUnmap at h
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at h; cases h
  | some table =>
    rw [hT] at h
    simp only at h
    split at h
    · cases h; exact hI
    · split at h
      · exact storeObject_preserves_objects_invExt _ _ _ _ hI h
      · split at h
        · split at h
          · cases h
          · cases hS1 : storeObject tableId (.pageTable table.uninstalled) st with
            | error e => rw [hS1] at h; cases h
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at h
              have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hI hS1
              exact storeObject_preserves_objects_invExt _ _ _ _
                (by rw [Architecture.recordPhysicalWrites_objects]; exact hI1) h
        · exact storeObject_preserves_objects_invExt _ _ _ _ hI h

theorem pageTableMap_mappingStage {tableId rootId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState} (h : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    MappingStage st st' :=
  MappingStage.of_kindPreservingWrite (fun hI => pageTableMap_objects_invExt hI h)
    fun hI => pageTableMap_kindPreservingWrite hI h

theorem pageTableUnmap_mappingStage {tableId : SeLe4n.ObjId} {st st' : SystemState}
    (h : Architecture.pageTableUnmap tableId st = .ok ((), st')) : MappingStage st st' :=
  MappingStage.of_kindPreservingWrite (fun hI => pageTableUnmap_objects_invExt hI h)
    fun hI => pageTableUnmap_kindPreservingWrite hI h

/-! ### The delete chains and the thread-space set -/

theorem cspaceRevokeCdtFinalising_mappingStage {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (P : MappingArmPremises st)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) : MappingStage st st' :=
  MappingStage.of_preserves (fun _ => objects_invExt_of_capabilityInvariantBundle _
      (cspaceRevokeCdtFinalising_preserves_capabilityInvariantBundle ec addr st st' P.caps h))
    (fun _ hL => cspaceRevokeCdtFinalising_preserves_liveMappingsRecorded ec addr st st' P.caps
      P.teardown hL h)
    fun hI hB => cspaceRevokeCdtFinalising_preserves_bookkeepingAgrees ec hI hB h

theorem cspaceDeleteSlotZombie_mappingStage {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (P : MappingArmPremises st)
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) : MappingStage st st' :=
  MappingStage.of_preserves (fun _ => objects_invExt_of_capabilityInvariantBundle _
      (cspaceDeleteSlotZombie_preserves_capabilityInvariantBundle ec addr st st' P.caps h))
    (fun _ hL => cspaceDeleteSlotZombie_preserves_liveMappingsRecorded ec addr st st' P.caps
      P.teardown hL h)
    fun hI hB => cspaceDeleteSlotZombie_preserves_bookkeepingAgrees ec hI hB h

theorem copyThreadSpacesZombie_mappingStage {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} (P : MappingArmPremises st)
    (h : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') : MappingStage st st' :=
  MappingStage.of_preserves (fun _ => objects_invExt_of_capabilityInvariantBundle _
      (copyThreadSpacesZombie_preserves_capabilityInvariantBundle ec P.caps h))
    (fun _ hL => copyThreadSpacesZombie_preserves_liveMappingsRecorded ec P.caps P.teardown hL h)
    fun hI hB => copyThreadSpacesZombie_preserves_bookkeepingAgrees ec hI hB h

end SeLe4n.Kernel
