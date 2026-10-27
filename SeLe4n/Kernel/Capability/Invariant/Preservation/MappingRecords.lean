-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.MappingRecords
import SeLe4n.Kernel.Capability.Invariant.Preservation.Revoke

/-! # The final delete keeps every live mapping recorded

The finalising delete destroys one capability, and with it the record that
capability held (`Capability.mapping`).  It also unmaps the page that record
names (`cspaceDeleteSlotFinalising_ok_unmapped`), so the mapping the record
witnessed is gone with it: a mapping still live afterwards was witnessed by a
capability in another slot, which the delete keeps.  The retire then erases the
object the destroyed capability was final to; a frame witnessing a live mapping
is named by that other slot too, so it is not that object.

So the delete keeps `SystemState.liveMappingsRecorded` on a state whose
capability invariants and teardown well-formedness hold
(`cspaceDeleteSlotFinalising_preserves_liveMappingsRecorded`), and so do the
revocation and the zombie delete, chains of such deletes.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A frame is no object a finalisation writes. -/
theorem not_finaliseWritableAny_frame (f : FrameObject) :
    ¬ finaliseWritableAny (.frame f) := by
  simp [finaliseWritableAny, finaliseWritable, KernelObject.objectType]

/-- **The roots' mapping half of `vspaceRootsShrink`.** -/
theorem vspaceRootsShrink.mappingRoots {st st' : SystemState} (h : vspaceRootsShrink st st') :
    SystemState.mappingRootsShrink st st' := fun rid r' hR => by
  obtain ⟨r, hr, ha, hm, he, -⟩ := h rid r' hR
  exact ⟨r, hr, ha, hm, he⟩

/-- **The finalisation keeps the mappings recorded**: it keeps every root, every
frame and every slot's capability (`FinaliseFrameAny`). -/
theorem FinaliseFrameAny.liveMappingsRecorded {st st' : SystemState} (h : FinaliseFrameAny st st')
    (hL : st.liveMappingsRecorded) : st'.liveMappingsRecorded :=
  SystemState.liveMappingsRecorded.of_shrink
    (fun rid r' hR => ⟨r', (h.write.roots_iff rid r').1 hR, rfl, fun _ _ hm => hm, fun _ _ he => he⟩)
    (SystemState.mappingRecordsKept.of_fwd
      (fun r cap hc _ => ⟨r, cap, (h.slotCapAt r).trans hc, rfl, rfl⟩)
      (fun _ f hf => ⟨f, h.write.keeps hf (not_finaliseWritableAny_frame f), rfl⟩))
    hL

theorem finaliseFinalObject_preserves_liveMappingsRecorded (target : Nat) (st : SystemState)
    (hInv : st.objects.invExt) (hL : st.liveMappingsRecorded) :
    (finaliseFinalObject target st).liveMappingsRecorded :=
  (finaliseFinalObject_frame target st hInv).liveMappingsRecorded hL

/-- **The delete keeps every frame**: it writes a CNode or a thread where one
stands, then derivation links. -/
theorem cspaceDeleteSlot_keeps_frame {addr : CSpaceAddr} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (h : cspaceDeleteSlot addr st = .ok ((), st'))
    {fid : SeLe4n.ObjId} {f : FrameObject} (hf : st.objects[fid]? = some (.frame f)) :
    st'.objects[fid]? = some (.frame f) := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  obtain ⟨o, hO, hH, hS⟩ := cspaceDeleteSlotCore_ok hC
  have hfC : stC.objects[fid]? = some (.frame f) := by
    by_cases hK : fid = addr.cnode
    · subst hK; rw [hO] at hf; cases hf; simp [KernelObject.holdsSlots] at hH
    · rwa [storeObject_objects_ne st _ _ fid _ hK hObjInv hS]
  have hInvC := storeObject_preserves_objects_invExt st _ _ _ hObjInv hS
  rcases (spliceDeletedCdtNode_reach stC addr).agree hInvC fid with
    hE | ⟨cn, cn', h1, h2, -⟩ | ⟨t, t', h1, h2, -⟩
  · rw [hE]; exact hfC
  all_goals first | (rw [h1] at hfC; cases hfC) | (rw [h2] at hfC; cases hfC)

/-- **The teardown keeps every frame**: it writes roots only. -/
theorem vspaceRootOnlyWrite.keeps_frame {st st' : SystemState} (h : vspaceRootOnlyWrite st st')
    {fid : SeLe4n.ObjId} {f : FrameObject} (hf : st.objects[fid]? = some (.frame f)) :
    st'.objects[fid]? = some (.frame f) := by
  rcases h fid with e | ⟨⟨r, hr⟩, -⟩
  · rw [e]; exact hf
  · rw [hf] at hr; cases hr

/-- **The retire keeps every frame but its target.** -/
theorem retireFinalObject_keeps_frame (ec : Concurrency.CoreId) (target recorder : Nat)
    (st : SystemState) (hInv : st.objects.invExt) {fid : SeLe4n.ObjId} {f : FrameObject}
    (hf : st.objects[fid]? = some (.frame f)) :
    (retireFinalObject ec target recorder st).objects[fid]? = some (.frame f) ∨
      (target ≠ 0 ∧ fid = SeLe4n.ObjId.ofNat (target - 1)) := by
  by_cases h0 : target = 0
  · subst h0; rw [retireFinalObject_zero]; exact .inl hf
  rcases (retireFinalObject_frame ec target recorder st hInv).2.2.2.2 fid with
    e | ⟨hx, -, -⟩ | ⟨U, U', -, hU, -⟩
  · rw [e]; exact .inl hf
  · exact .inr ⟨h0, hx⟩
  · rw [hf] at hU; cases hU

/-- **The finalising delete keeps every live mapping recorded.**  A mapping
live after the delete was live before it (the delete only shrinks roots), so a
slot recorded it.  That slot is not the one deleted: the delete unmapped the
page the deleted capability recorded (`cspaceDeleteSlotFinalising_ok_unmapped`),
and on the well-formed post-state the mapping's own root is the one its ASID
resolves to, where the mapping is still live.  So the recording slot keeps its
capability, and the frame it names is kept: the retire erases only the object
the deleted capability was final to, which no other slot names
(`slotRetireTarget_spec`). -/
theorem cspaceDeleteSlotFinalising_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (hW : teardownWellFormed st) (hL : st.liveMappingsRecorded)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    st'.liveMappingsRecorded := by
  have hW' := cspaceDeleteSlotFinalising_preserves_teardownWellFormed ec hW h
  have hS := cspaceDeleteSlotFinalising_shrinks ec hW h
  have hUnmapped := cspaceDeleteSlotFinalising_ok_unmapped ec addr st st' hW h
  obtain ⟨st1, st2, hD, hF, hEq⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  obtain ⟨-, hC1, -⟩ := cspaceDeleteSlot_slots hW.1 hD
  have hInv1 := cspaceDeleteSlot_preserves_capabilityInvariantBundle st st1 addr hInv hD
  obtain ⟨hI2, -, hC2, -, hV2⟩ :=
    finaliseDestroyedCapabilities_slots ec _ _ st1 st2 hInv1.2.2.2.2.1 hF
  have hFr := finaliseFinalObject_frame (slotRetireTarget st addr.cnode addr.slot) st2 hI2
  intro rid r' v p perms e hR hM hE
  obtain ⟨r, hr, ha, hm, he, -⟩ := hS rid r' hR
  obtain ⟨s, cap, fid, f, hc, ht, hf, hb, hmap⟩ :=
    hL rid r v p perms e hr (hm v _ hM) (he v e hE)
  by_cases hs : s = addr
  · subst hs
    exfalso
    have hP : capabilityMappedPage st cap = some ⟨r.asid, v, p, some e⟩ := by
      have hG : st.getFrame? fid = some f := (SystemState.getFrame?_eq_some_iff st fid f).2 hf
      simp [capabilityMappedPage, hmap, ht, hG, hb]
    have hNot := hUnmapped cap hc _ hP
    have hRes := resolveAsidRoot_of_root hW' hR
    rw [ha] at hRes
    unfold mappedPageLive at hNot
    simp only [hRes, VSpaceRoot.lookup, hM, hE] at hNot
    simp at hNot
  · refine ⟨s, cap, fid, f, ?_, ht, ?_, hb, ha ▸ hmap⟩
    · rw [hEq]
      unfold retireFinalisedObject
      rw [retireFinalObject_slotCapAt _ _ _ _ hFr.invExt, hFr.slotCapAt, hC2, hC1 s hs]
      exact hc
    · have hf2 := hV2.keeps_frame (cspaceDeleteSlot_keeps_frame hW.1 hD hf)
      have hf3 := hFr.write.keeps hf2 (not_finaliseWritableAny_frame f)
      rw [hEq]
      unfold retireFinalisedObject
      rcases retireFinalObject_keeps_frame ec _ (slotRetireRecorder st addr.cnode addr.slot) _
          hFr.invExt hf3 with hk | ⟨hT, hx⟩
      · exact hk
      · exfalso
        obtain ⟨c, hc0, hn, hFin⟩ := slotRetireTarget_spec hInv hT
        have hAddr : SystemState.namesAt st.slotCapAt ⟨addr.cnode, addr.slot⟩
            (SeLe4n.ObjId.ofNat (slotRetireTarget st addr.cnode addr.slot - 1)) := ⟨c, hc0, hn⟩
        exact hFin _ hAddr s hs ⟨cap, hc, by rw [← hx]; simp [Capability.namedObject, ht]⟩

/-- **What a finalising delete chain carries**: the capability invariants, the
teardown's well-formedness and the mapping records together, each step's
preservation of the third reading the first two. -/
def mappingRecordsCarried (st : SystemState) : Prop :=
  capabilityInvariantBundle st ∧ teardownWellFormed st ∧ st.liveMappingsRecorded

theorem cspaceDeleteSlotFinalising_preserves_mappingRecordsCarried (ec : Concurrency.CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (h : mappingRecordsCarried st)
    (hD : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) : mappingRecordsCarried st' :=
  ⟨cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle ec addr st st' h.1 hD,
    cspaceDeleteSlotFinalising_preserves_teardownWellFormed ec h.2.1 hD,
    cspaceDeleteSlotFinalising_preserves_liveMappingsRecorded ec addr st st' h.1 h.2.1 h.2.2 hD⟩

theorem finaliseFinalObject_preserves_mappingRecordsCarried (target : Nat) (st : SystemState)
    (h : mappingRecordsCarried st) : mappingRecordsCarried (finaliseFinalObject target st) :=
  ⟨finaliseFinalObject_preserves_capabilityInvariantBundle target st h.1,
    (finaliseFinalObject_preserves_teardownWellFormed target st h.2.1).1,
    finaliseFinalObject_preserves_liveMappingsRecorded target st h.2.1.1 h.2.2⟩

/-- **The finalising revocation keeps every live mapping recorded**: a run of
finalising deletes (`cspaceRevokeCdtFinalising_closed`). -/
theorem cspaceRevokeCdtFinalising_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (hW : teardownWellFormed st) (hL : st.liveMappingsRecorded)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    st'.liveMappingsRecorded :=
  (cspaceRevokeCdtFinalising_closed mappingRecordsCarried
    (cspaceDeleteSlotFinalising_preserves_mappingRecordsCarried ec)
    finaliseFinalObject_preserves_mappingRecordsCarried ⟨hInv, hW, hL⟩ h).2.2

/-- **The zombie delete keeps every live mapping recorded**: a chain of
finalising deletes and finalisations (`cspaceDeleteSlotZombie_closed`). -/
theorem cspaceDeleteSlotZombie_preserves_liveMappingsRecorded (ec : Concurrency.CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (hW : teardownWellFormed st) (hL : st.liveMappingsRecorded)
    (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    st'.liveMappingsRecorded :=
  (cspaceDeleteSlotZombie_closed mappingRecordsCarried
    (cspaceDeleteSlotFinalising_preserves_mappingRecordsCarried ec)
    finaliseFinalObject_preserves_mappingRecordsCarried ⟨hInv, hW, hL⟩ h).2.2

end SeLe4n.Kernel
