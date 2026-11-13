-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.SetSpaceMappingRecords

/-! # The capability arms keep the bookkeeping in agreement

WS-UC UC2: the object index, its set and the type table are ghosts that agree
with the object table (`SystemState.bookkeepingAgrees`).  Every capability
write is a store (`storeObject_preserves_bookkeepingAgrees`), a derivation-link
write (`linkReach.bookkeepingAgrees`) or an erase
(`withObjectErased_preserves_bookkeepingAgrees`), so each operation keeps the
agreement on a state whose object table is well formed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ### Slot writes -/

theorem cspaceInsertSlot_preserves_bookkeepingAgrees {addr : CSpaceAddr} {cap : Capability}
    {st st' : SystemState} (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : cspaceInsertSlot addr cap st = .ok ((), st')) : st'.bookkeepingAgrees := by
  obtain ⟨_, _, _, _, hS⟩ := cspaceInsertSlot_ok_decompose st st' addr cap h
  exact storeObject_preserves_bookkeepingAgrees _ _ _ _ hB hInv hS

theorem setCapFreeIndex_preserves_bookkeepingAgrees {st : SystemState} {addr : CSpaceAddr}
    {idx : Nat} (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees) :
    (setCapFreeIndex st addr idx).bookkeepingAgrees := by
  cases hO : st.objects[addr.cnode]? with
  | none => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]; exact hB
  | some o =>
    cases o with
    | cnode cn =>
      exact storeObject_preserves_bookkeepingAgrees _ _ _ _ hB hInv
        (setCapFreeIndex_eq_storeObject (idx := idx) hO)
    | _ => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]; exact hB

theorem untypedSourceSetFull_preserves_bookkeepingAgrees {st : SystemState} {src : CSpaceAddr}
    {cap : Capability} (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees) :
    (untypedSourceSetFull st src cap).bookkeepingAgrees :=
  untypedSourceSetFull_of (P := SystemState.bookkeepingAgrees) hB
    fun _ => setCapFreeIndex_preserves_bookkeepingAgrees hInv hB

theorem cdtAddChild_preserves_bookkeepingAgrees {st : SystemState} {p c : SlotRef}
    {op : DerivationOp} (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees) :
    (st.cdtAddChild p c op).bookkeepingAgrees :=
  (SystemState.cdtAddChild_reach st p c op).bookkeepingAgrees hInv
    (hB.of_objects_ghosts rfl ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩)

theorem cdtMove_preserves_bookkeepingAgrees {st : SystemState} {old new : SlotRef}
    (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees) :
    (st.cdtMove old new).bookkeepingAgrees :=
  (SystemState.cdtMove_reach st old new).bookkeepingAgrees hInv
    (hB.of_objects_ghosts rfl ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩)

theorem cspaceDeleteSlotCore_preserves_bookkeepingAgrees {addr : CSpaceAddr}
    {st st' : SystemState} (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : cspaceDeleteSlotCore addr st = .ok ((), st')) : st'.bookkeepingAgrees := by
  obtain ⟨_, _, _, hS⟩ := cspaceDeleteSlotCore_ok h
  exact storeObject_preserves_bookkeepingAgrees _ _ _ _ hB hInv hS

/-- The delete: the slot emptied, then its derivation node spliced out. -/
theorem cspaceDeleteSlot_preserves_bookkeepingAgrees {addr : CSpaceAddr}
    {st st' : SystemState} (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : cspaceDeleteSlot addr st = .ok ((), st')) :
    st'.objects.invExt ∧ st'.bookkeepingAgrees := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  obtain ⟨_, _, _, hS⟩ := cspaceDeleteSlotCore_ok hC
  have hIC := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
  exact ⟨(spliceDeletedCdtNode_reach stC addr).invExt hIC,
    (spliceDeletedCdtNode_reach stC addr).bookkeepingAgrees hIC
      ((cspaceDeleteSlotCore_preserves_bookkeepingAgrees hInv hB hC).of_objects_ghosts rfl
        ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩)⟩

theorem cspaceCopy_preserves_bookkeepingAgrees {src dst : CSpaceAddr} {mask : AccessRightSet} {st st' : SystemState}
    (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : cspaceCopy src dst mask st = .ok ((), st')) : st'.bookkeepingAgrees := by
  obtain ⟨cap, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose h
  have hI2 := cspaceInsertSlot_objects_invExt hInv hIns
  exact untypedSourceSetFull_preserves_bookkeepingAgrees
    ((SystemState.cdtAddChild_reach st2 src dst .copy).invExt hI2)
    (cdtAddChild_preserves_bookkeepingAgrees hI2
      (cspaceInsertSlot_preserves_bookkeepingAgrees hInv hB hIns))

theorem cspaceMintWithCdt_preserves_bookkeepingAgrees {src dst : CSpaceAddr}
    {rights : AccessRightSet} {badge : Option SeLe4n.Badge} {st st' : SystemState}
    (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    st'.bookkeepingAgrees := by
  unfold cspaceMintWithCdt at h
  cases hM : cspaceMint src dst rights badge st with
  | error e => rw [hM] at h; cases h
  | ok pr =>
    obtain ⟨⟨⟩, st1⟩ := pr
    rw [hM] at h
    obtain ⟨-, child, -, hIns, -⟩ := cspaceMint_ok_decompose src dst rights badge st st1 hM
    have hI1 := cspaceInsertSlot_objects_invExt hInv hIns
    have hB1 := cspaceInsertSlot_preserves_bookkeepingAgrees hInv hB hIns
    simp only at h
    split at h
    · split at h
      · cases h
      · cases h
        exact untypedSourceSetFull_preserves_bookkeepingAgrees
          ((SystemState.cdtAddChild_reach st1 src dst .mint).invExt hI1)
          (cdtAddChild_preserves_bookkeepingAgrees hI1 hB1)
    · cases h
      exact cdtAddChild_preserves_bookkeepingAgrees hI1 hB1

/-- The move: the capability inserted at the destination, the source emptied,
then the derivation node moved. -/
theorem cspaceMove_preserves_bookkeepingAgrees {src dst : CSpaceAddr} {st st' : SystemState}
    (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : cspaceMove src dst st = .ok ((), st')) : st'.bookkeepingAgrees := by
  unfold cspaceMove at h
  by_cases hSelf : src = dst
  · simp [hSelf] at h
  simp only [hSelf, ↓reduceIte] at h
  cases hSrc : cspaceLookupSlot src st with
  | error e => rw [hSrc] at h; cases h
  | ok pair =>
    obtain ⟨cap, st1⟩ := pair
    have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src cap hSrc
    subst hSt1
    rw [hSrc] at h
    simp only at h
    cases hNN : cap.toNonNull? with
    | none => rw [hNN] at h; cases h
    | some capNN =>
      rw [hNN] at h
      simp only at h
      cases hIns : cspaceInsertSlot dst capNN.val st1 with
      | error e => rw [hIns] at h; cases h
      | ok pr2 =>
        obtain ⟨⟨⟩, st2⟩ := pr2
        rw [hIns] at h
        simp only at h
        cases hDel : cspaceDeleteSlotCore src st2 with
        | error e => rw [hDel] at h; cases h
        | ok pr3 =>
          obtain ⟨⟨⟩, st3⟩ := pr3
          rw [hDel] at h
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
          subst h
          have hI2 := cspaceInsertSlot_objects_invExt hInv hIns
          have hB3 := cspaceDeleteSlotCore_preserves_bookkeepingAgrees hI2
            (cspaceInsertSlot_preserves_bookkeepingAgrees hInv hB hIns) hDel
          obtain ⟨o, -, -, hS3⟩ := cspaceDeleteSlotCore_ok hDel
          exact cdtMove_preserves_bookkeepingAgrees
            (storeObject_preserves_objects_invExt _ _ _ _ hI2 hS3) hB3

theorem mintReplyCapWithCdt_preserves_bookkeepingAgrees {src dst : CSpaceAddr}
    {st st' : SystemState} (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : mintReplyCapWithCdt src dst st = .ok ((), st')) : st'.bookkeepingAgrees := by
  unfold mintReplyCapWithCdt at h
  cases hM : mintReplyCap src dst st with
  | error e => rw [hM] at h; cases h
  | ok pr =>
    obtain ⟨⟨⟩, st1⟩ := pr
    rw [hM] at h
    cases h
    unfold mintReplyCap at hM
    cases hLk : cspaceLookupSlot src st with
    | error e => rw [hLk] at hM; cases hM
    | ok pair =>
      obtain ⟨parent, st0⟩ := pair
      have hSt0 : st0 = st := cspaceLookupSlot_preserves_state st st0 src parent hLk
      subst hSt0
      rw [hLk] at hM
      simp only at hM
      split at hM
      · split at hM
        · exact cdtAddChild_preserves_bookkeepingAgrees (cspaceInsertSlot_objects_invExt hInv hM)
            (cspaceInsertSlot_preserves_bookkeepingAgrees hInv hB hM)
        · cases hM
      · cases hM


/-! ### The finalisation's teardown -/

/-- A step that writes roots as roots and none of the ghosts keeps the agreement. -/
theorem _root_.SeLe4n.Model.SystemState.bookkeepingAgrees.of_vspaceRootOnlyWrite
    {st st' : SystemState} (h : st.bookkeepingAgrees) (hW : vspaceRootOnlyWrite st st')
    (hG : SystemState.ghostsKept st' st) : st'.bookkeepingAgrees :=
  h.of_kept ⟨hG.index, hG.indexSet, hG.types, fun x => by
    rcases hW x with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
    · rw [e]
    · rw [hr, hr']; rfl, hG.objectsCapacity, hG.asidCapacity⟩

/-- A store over an object of the same kind moves no ghost. -/
theorem storeObjectState_ghostsKept {id : SeLe4n.ObjId} {obj old : KernelObject}
    {st : SystemState} (hOld : st.objects[id]? = some old) (hK : old.objectType = obj.objectType) :
    SystemState.ghostsKept (storeObjectState id obj st) st :=
  .storeObject_sameKind (storeObject_eq_storeObjectState id obj st) hOld hK

/-- One page's unmap writes the root the ASID resolves to, as a root. -/
theorem unmapPageState_ghostsKept (ec : Concurrency.CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (st : SystemState) :
    SystemState.ghostsKept (unmapPageState ec asid vaddr st) st := by
  unfold unmapPageState
  split
  · exact .refl _
  · next rootId root hR =>
    split
    · exact .refl _
    · next root' _ =>
      have hO := (Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hR).2.1
      have hG : SystemState.ghostsKept (storeObjectState rootId (.vspaceRoot root')
          (Architecture.recordPhysicalWrites st (Architecture.mappingStore? st root' vaddr).toList))
          st :=
        (storeObjectState_ghostsKept (old := .vspaceRoot root) (obj := .vspaceRoot root')
          (st := Architecture.recordPhysicalWrites st (Architecture.mappingStore? st root' vaddr).toList)
          (by rw [Architecture.recordPhysicalWrites_objects]; exact hO) rfl).trans ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
      dsimp only
      split <;> exact ⟨hG.index, hG.indexSet, hG.types, hG.objectsCapacity, hG.asidCapacity⟩

theorem unmapLivePagesState_ghostsKept (ec : Concurrency.CoreId) :
    ∀ (ps : List MappedPage) (st : SystemState),
      SystemState.ghostsKept (unmapLivePagesState ec ps st) st
  | [], _ => .refl _
  | p :: rest, st => by
    unfold unmapLivePagesState
    split
    · exact (unmapLivePagesState_ghostsKept ec rest _).trans (unmapPageState_ghostsKept ..)
    · exact unmapLivePagesState_ghostsKept ec rest st

theorem detachPageTablesState_ghostsKept :
    ∀ (os : List (SeLe4n.ObjId × PageTableInstall)) (st : SystemState),
      SystemState.ghostsKept (detachPageTablesState os st) st
  | [], _ => .refl _
  | o :: rest, st => by
    unfold detachPageTablesState
    split
    · exact detachPageTablesState_ghostsKept rest st
    · next root hR =>
      have hO := (SystemState.getVSpaceRoot?_eq_some_iff st o.2.root root).mp hR
      exact (detachPageTablesState_ghostsKept rest _).trans
        ((storeObjectState_ghostsKept (old := .vspaceRoot root)
          (obj := .vspaceRoot (root.withoutTablesBeneath o.2 o.1))
          (st := Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1))
          (by rw [Architecture.recordPhysicalWrites_objects]; exact hO) rfl).trans ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩)

/-- **The teardown keeps the agreement**: it writes roots as roots and no ghost. -/
theorem finaliseDestroyedCapabilities_preserves_bookkeepingAgrees (ec : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) {st st' : SystemState}
    (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    st'.objects.invExt ∧ st'.bookkeepingAgrees := by
  obtain ⟨hI', -, -, -, hV⟩ := finaliseDestroyedCapabilities_slots ec _ _ st st' hInv h
  have hG : SystemState.ghostsKept st' st := by
    rw [finaliseDestroyedCapabilities_eq_ok_state] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    unfold finaliseDestroyedCapabilitiesState
    exact (unmapLivePagesState_ghostsKept ec _ _).trans (detachPageTablesState_ghostsKept _ _)
  exact ⟨hI', hB.of_vspaceRootOnlyWrite hV hG⟩

/-! ### The retire -/

theorem storeUntypedWith_preserves_bookkeepingAgrees (st : SystemState) (w : SeLe4n.ObjId)
    (f : UntypedObject → UntypedObject) (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees) :
    (st.storeUntypedWith w f).bookkeepingAgrees := by
  cases hW : st.objects[w]? with
  | none => unfold SystemState.storeUntypedWith; rw [hW]; exact hB
  | some o =>
    cases o with
    | untyped U =>
      exact storeObject_preserves_bookkeepingAgrees _ _ _ _ hB hInv
        (SystemState.storeObject_untyped_eq_storeUntypedWith hW f)
    | _ => all_goals (unfold SystemState.storeUntypedWith; rw [hW]; exact hB)

theorem reparentChildren_preserves_bookkeepingAgrees (recorder : Nat) :
    ∀ (kids : List UntypedChild) (st : SystemState), st.objects.invExt →
      st.objects.size < st.objects.capacity → st.bookkeepingAgrees →
      (reparentChildren recorder kids st).bookkeepingAgrees
  | [], _, _, _, hB => hB
  | c :: rest, st, hInv, hSz, hB => by
    simp only [reparentChildren]
    obtain ⟨hI1, hS1, -⟩ := storeUntypedWith_frame st c.objId
      (fun U => { U with parent := recorderParent recorder }) hInv hSz
    exact reparentChildren_preserves_bookkeepingAgrees recorder rest _ hI1 hS1
      (storeUntypedWith_preserves_bookkeepingAgrees _ _ _ hInv hB)

theorem retireUnrecord_preserves_bookkeepingAgrees (recorder : Nat) (x : SeLe4n.ObjId)
    (st : SystemState) (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity)
    (hB : st.bookkeepingAgrees) : (retireUnrecord recorder x st).bookkeepingAgrees := by
  have hR := reparentChildren_preserves_bookkeepingAgrees recorder (retiredChildren st x) st
    hInv hSz hB
  obtain ⟨hI0, -⟩ := reparentChildren_frame recorder (retiredChildren st x) st hInv hSz
  unfold retireUnrecord adoptChildren
  dsimp only
  split
  · exact hR
  · exact storeUntypedWith_preserves_bookkeepingAgrees _ _ _ hI0 hR

theorem retireCarvedObject_preserves_bookkeepingAgrees (st : SystemState) (id : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hSz : st.objects.size < st.objects.capacity)
    (hB : st.bookkeepingAgrees) : (retireCarvedObject st id).bookkeepingAgrees := by
  unfold retireCarvedObject
  split
  · exact (withObjectErased_preserves_bookkeepingAgrees st id hB hInv hSz).of_objects_ghosts rfl
      ⟨rfl, rfl, rfl, Nat.le_refl _, by
        show st.asidTable.capacity ≤ (match st.getVSpaceRoot? id with
          | some root => st.asidTable.erase root.asid | none => st.asidTable).capacity
        split <;> simp⟩
  · exact hB

theorem retireRecordedObject_preserves_bookkeepingAgrees (ec : Concurrency.CoreId)
    (recorder : Nat) (x : SeLe4n.ObjId) (st : SystemState) (hInv : st.objects.invExt)
    (hSz : st.objects.size < st.objects.capacity) (hB : st.bookkeepingAgrees) :
    (retireRecordedObject ec recorder x st).bookkeepingAgrees := by
  obtain ⟨i1, room1, -⟩ := retireUnrecord_frame recorder x st hInv hSz
  have hB1 := retireUnrecord_preserves_bookkeepingAgrees recorder x st hInv hSz hB
  have hB2 := retireCarvedObject_preserves_bookkeepingAgrees _ x i1 room1 hB1
  unfold retireRecordedObject
  dsimp only
  split
  · exact hB2.of_objects_ghosts (asidReleaseRound_objects _ _ _) ⟨rfl, rfl, rfl, by rw [asidReleaseRound_objects]; exact Nat.le_refl _,
      by capacity_kept⟩
  · exact hB2

theorem retireFinalObject_preserves_bookkeepingAgrees (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hInv : st.objects.invExt)
    (hB : st.bookkeepingAgrees) : (retireFinalObject ec target recorder st).bookkeepingAgrees := by
  unfold retireFinalObject
  split
  · exact hB
  split
  · next hSz =>
    dsimp only
    split
    · obtain ⟨i0, room0, -⟩ := eraseRetiredObject_frame st _ hInv hSz
      refine retireRecordedObject_preserves_bookkeepingAgrees ec recorder _ _ i0 room0 ?_
      unfold eraseRetiredObject
      split
      · exact withObjectErased_preserves_bookkeepingAgrees st _ hB hInv hSz
      · exact hB
    · exact hB
  · exact hB

/-- **The finalising delete keeps the agreement**: the delete, the teardown, and
the retire — a node's line, or the finalisation and the object's erase. -/
theorem cspaceDeleteSlotFinalising_preserves_bookkeepingAgrees (ec : Concurrency.CoreId)
    {addr : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hB : st.bookkeepingAgrees) (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    st'.objects.invExt ∧ st'.bookkeepingAgrees := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  obtain ⟨hI1, hB1⟩ := cspaceDeleteSlot_preserves_bookkeepingAgrees hInv hB hD
  obtain ⟨hI2, hB2⟩ := finaliseDestroyedCapabilities_preserves_bookkeepingAgrees ec _ _ hI1 hB1 hF
  rcases retireFinalisedObject_cases ec (slotRetireTarget st addr.cnode addr.slot)
      (slotRetireRecorder st addr.cnode addr.slot) st2 with ⟨-, hR⟩ | ⟨-, hR⟩
  · rw [hR]
    refine ⟨by rw [retireIrqNode_objects]; exact hI2,
      hB2.of_objects_ghosts (retireIrqNode_objects _ _) ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact Architecture.setIrqLineSignal_objectIndex _ _ _
    · exact Architecture.setIrqLineSignal_objectIndexSet _ _ _
    · exact congrArg (·.objectTypes) (Architecture.setIrqLineSignal_lifecycle _ _ _)
    · rw [retireIrqNode_objects]; exact Nat.le_refl _
    · exact Nat.le_of_eq (congrArg RobinHood.RHTable.capacity
        (Architecture.setIrqLineSignal_asidTable _ _ _)).symm
  · rw [hR]
    have hFr := finaliseReleased_frame (slotRetireTarget st addr.cnode addr.slot) st2 hI2
    exact ⟨(retireFinalObject_frame ec _ _ _ hFr.invExt).1,
      retireFinalObject_preserves_bookkeepingAgrees ec _ _ _ hFr.invExt (hFr.bookkeepingAgrees hB2)⟩

theorem finaliseFinalObject_preserves_bookkeepingAgrees (target : Nat) (st : SystemState)
    (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees) :
    (finaliseFinalObject target st).objects.invExt ∧
      (finaliseFinalObject target st).bookkeepingAgrees :=
  have hF := finaliseFinalObject_frame target st hInv
  ⟨hF.invExt, hF.bookkeepingAgrees hB⟩

/-- **The finalising revocation keeps the agreement**: a run of finalising
deletes and finalisations. -/
theorem cspaceRevokeCdtFinalising_preserves_bookkeepingAgrees (ec : Concurrency.CoreId)
    {addr : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hB : st.bookkeepingAgrees) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    st'.bookkeepingAgrees :=
  (cspaceRevokeCdtFinalising_closed (fun s => s.objects.invExt ∧ s.bookkeepingAgrees)
    (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_preserves_bookkeepingAgrees ec hQ.1 hQ.2 hD)
    (fun t s hQ => finaliseFinalObject_preserves_bookkeepingAgrees t s hQ.1 hQ.2) ⟨hInv, hB⟩ h).2

/-- **The zombie delete keeps the agreement**: a chain of finalising deletes and
finalisations. -/
theorem cspaceDeleteSlotZombie_preserves_bookkeepingAgrees (ec : Concurrency.CoreId)
    {addr : CSpaceAddr} {st st' : SystemState} (hInv : st.objects.invExt)
    (hB : st.bookkeepingAgrees) (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    st'.bookkeepingAgrees :=
  (cspaceDeleteSlotZombie_closed (fun s => s.objects.invExt ∧ s.bookkeepingAgrees)
    (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_preserves_bookkeepingAgrees ec hQ.1 hQ.2 hD)
    (fun t s hQ => finaliseFinalObject_preserves_bookkeepingAgrees t s hQ.1 hQ.2) ⟨hInv, hB⟩ h).2

/-! ### The thread-space set -/

theorem threadSlotCopied_preserves_bookkeepingAgrees {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (data : UInt64)
    (hB : st.bookkeepingAgrees) :
    (threadSlotCopied st tid slot srcCNode srcSlot rights data).bookkeepingAgrees := by
  have hS := threadSlotCleared_store hT slot
  have hInvC := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
  have hBC := storeObject_preserves_bookkeepingAgrees _ _ _ _ hB hInv hS
  have hR := spliceDeletedCdtNode_reach (threadSlotCleared tid.toObjId slot st)
    { cnode := tid.toObjId, slot := slot }
  have hBD := hR.bookkeepingAgrees hInvC (hBC.of_objects_ghosts rfl ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩)
  have hID := hR.invExt hInvC
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights data with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e]; exact hBD
  · rw [e]
    exact cdtAddChild_preserves_bookkeepingAgrees
      (SystemState.updateTcb_preserves_objects_invExt _ tid _ hID)
      (hBD.of_kept (SystemState.BookkeepingKept.updateTcb _ _ _ hID))

theorem threadSlotSet_preserves_bookkeepingAgrees (ec : Concurrency.CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hInv : st.objects.invExt) (hT : st.getTcb? tid = some t)
    (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (rights : AccessRightSet) (data : UInt64) (hB : st.bookkeepingAgrees) :
    (threadSlotSet ec st tid slot srcCNode srcSlot rights data).objects.invExt ∧
      (threadSlotSet ec st tid slot srcCNode srcSlot rights data).bookkeepingAgrees := by
  have hI := (threadSlotCopied_tcb hInv hT slot srcCNode srcSlot rights data).2
  unfold threadSlotSet
  dsimp only
  exact ⟨(retireFinalObject_frame ec _ _ _ hI).1, retireFinalObject_preserves_bookkeepingAgrees
    ec _ _ _ hI (threadSlotCopied_preserves_bookkeepingAgrees hInv hT slot srcCNode srcSlot rights data hB)⟩

theorem copyThreadSpaces_preserves_bookkeepingAgrees (ec : Concurrency.CoreId)
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} {cnData : UInt64}
    (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (hStep : copyThreadSpaces ec st vtid cnSrc vrSrc cnData = .ok st') :
    st'.objects.invExt ∧ st'.bookkeepingAgrees := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok hStep
  obtain ⟨hI1, hB1⟩ := threadSlotSet_preserves_bookkeepingAgrees ec hInv hT TCB.cspaceRootSlot
    cnSrc.cnode cnSrc.slot TCB.cspaceRootRights cnData hB
  obtain ⟨t1, hT1⟩ := cspaceRootSet_getTcb? ec hInv hT hCn
  exact threadSlotSet_preserves_bookkeepingAgrees ec hI1 hT1 TCB.vspaceRootSlot vrSrc.cnode
    vrSrc.slot TCB.vspaceRootRights 0 hB1

/-- **Setting a thread's space through the zombie delete keeps the agreement**:
finalising deletes and finalisations, then the plain space change. -/
theorem copyThreadSpacesZombie_preserves_bookkeepingAgrees (ec : Concurrency.CoreId)
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} {cnData : UInt64}
    (hInv : st.objects.invExt) (hB : st.bookkeepingAgrees)
    (hStep : copyThreadSpacesZombie ec st vtid cnSrc vrSrc cnData = .ok st') :
    st'.bookkeepingAgrees := by
  rcases copyThreadSpacesZombie_cases hStep with h1 | ⟨n, s, hR, rfl | h2⟩
  · exact (copyThreadSpaces_preserves_bookkeepingAgrees ec hInv hB h1).2
  · exact (hR.chain.closed (fun s => s.objects.invExt ∧ s.bookkeepingAgrees)
      (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_preserves_bookkeepingAgrees ec hQ.1 hQ.2 hD)
      (fun t s hQ => finaliseFinalObject_preserves_bookkeepingAgrees t s hQ.1 hQ.2)
      ⟨hInv, hB⟩).2
  · have hC := hR.chain.closed (fun s => s.objects.invExt ∧ s.bookkeepingAgrees)
      (fun _ _ _ hQ hD => cspaceDeleteSlotFinalising_preserves_bookkeepingAgrees ec hQ.1 hQ.2 hD)
      (fun t s hQ => finaliseFinalObject_preserves_bookkeepingAgrees t s hQ.1 hQ.2) ⟨hInv, hB⟩
    exact (copyThreadSpaces_preserves_bookkeepingAgrees ec hC.1 hC.2 h2).2

end SeLe4n.Kernel
