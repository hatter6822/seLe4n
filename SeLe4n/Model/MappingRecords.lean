-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.SlotTreeShape

/-! # Every live mapping is recorded on a capability to its frame

seL4's frame capability records where it mapped its frame (`capFMappedASID`,
`capFMappedAddress`), and destroying the capability unmaps it (`finaliseCap` →
`unmapPage`), so no mapping outlives the authority that made it.  Here a frame
capability records its mapping (`Capability.mapping`), and the final delete
removes the page the destroyed capability records before the retire erases the
frame (`cspaceDeleteSlotFinalising`).  That removes *every* mapping of the frame
only if every mapping is recorded somewhere: this module states that.

A mapping a capability made carries the frame's mapping epoch in its address
space (`VSpaceRoot.mappingEpochs`, written by `.vspaceMap` beside the
translation and erased with it by every unmap).  `liveMappingsRecorded` says
that every such mapping — an address an address space maps to a page, with an
epoch — is recorded on a capability held in some slot: one that targets a frame
whose base is the page, and whose record names the address space's ASID, the
address and the epoch.  The boot's own mappings (the kernel window of the
binding's root) carry no epoch: they name the kernel's reserved memory and its
devices, which no untyped describes, and no capability made them.

It also says that no thread's space slot holds a capability recording a
mapping (`threadSlotsRecordNoMapping`).  The thread-space set overwrites a
thread's slot without unmapping what the old capability records, so the
records survive it only because none is held there.  A step keeps that half
when every thread slot's capability after it was that slot's before, or records
nothing (`threadSlotsDrawnFrom`), and every frame lemma below carries it.

The invariant reads the slots' capabilities and the objects' mapping facts
(`KernelObject.mappingView`: a root's ASID, translations and epochs, a frame's
base).  So a step that keeps every key's kind and mapping facts and every
thread's slots, and writes no CNode — a `kindPreservingWrite` — keeps it
(`liveMappingsRecorded.of_kindPreservingWrite`), and so does any step whose
roots only lose translations and epochs and which keeps every record with its
frame (`liveMappingsRecorded.of_shrink`).  The writes that do more — the map,
which adds a recorded mapping; a capability move; the final delete, which
destroys a record and the frame; the thread-space set, which overwrites a
thread's slot — are proven beside them (`Kernel/MappingRecordPreservation.lean`,
`Capability/Invariant/Preservation/MappingRecords.lean` and
`SetSpaceMappingRecords.lean`).
-/

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood

namespace SystemState

/-- **A slot records the mapping of `vaddr` in address space `asid` to the page
`paddr` under epoch `epoch`**: some slot holds a capability that targets a frame
whose base is `paddr` and whose record names the ASID, the address and the
epoch. -/
def mappingRecordedAt (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (epoch : Nat) : Prop :=
  ∃ (r : SlotRef) (cap : Capability) (fid : SeLe4n.ObjId) (f : FrameObject),
    st.slotCapAt r = some cap ∧ cap.target = .object fid ∧
    st.objects[fid]? = some (.frame f) ∧ f.base = paddr ∧
    cap.mapping = some { asid := asid, vaddr := vaddr, epoch := epoch }

/-- **Every live mapping is witnessed by a capability to its frame.**  Every
address an address space maps under a mapping epoch is recorded on a capability
held in some slot, to the frame whose base the address maps to, naming the
address space's ASID, the address and the epoch (`mappingRecordedAt`).  The
final delete of a frame's last capability removes the mapping that capability
records, so on a state this holds in, no mapping a capability made outlives the
frame's retire. -/
def liveMappingsWitnessed (st : SystemState) : Prop :=
  ∀ (rid : SeLe4n.ObjId) (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) (epoch : Nat),
    st.objects[rid]? = some (.vspaceRoot root) →
    root.mappings[vaddr]? = some (paddr, perms) →
    root.mappingEpochs[vaddr]? = some epoch →
    st.mappingRecordedAt root.asid vaddr paddr epoch

/-- **No thread's space slot records a mapping**: every capability a thread's
CSpace or VSpace root slot holds carries no mapping record
(`Capability.mapping = none`).  The space set (`threadSlotCopied`) writes over
a thread's slot without unmapping what the old capability records, so a record
held there would be lost with its mapping still live.  None is: the set writes
`TCB.spaceCopyOf`, which carries no record (as seL4's `deriveCap` clears a frame
capability's mapped address), the carve writes empty slots, the insert, the map
and the transfer write CNode slots only, and the boot refuses a configured
record (`bootSafeCapCheck`). -/
def threadSlotsRecordNoMapping (st : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ObjId) (t : TCB) (s : SeLe4n.Slot) (cap : Capability),
    st.objects[tid]? = some (.tcb t) → t.spaceSlotCap s = some cap → cap.mapping = none

/-- **Every live mapping is recorded on a capability to its frame, held where
only a delete that unmaps it removes it.**  Every mapping an address space makes
under a mapping epoch is witnessed by a slot's capability
(`liveMappingsWitnessed`), and no thread's space slot holds a record
(`threadSlotsRecordNoMapping`): the second is what keeps the first through the
space set, which overwrites a thread's slot.  The final delete of a frame's last
capability removes the mapping that capability records, so on a state this
holds in, no mapping a capability made outlives the frame's retire. -/
def liveMappingsRecorded (st : SystemState) : Prop :=
  st.liveMappingsWitnessed ∧ st.threadSlotsRecordNoMapping

/-- **Every capability a thread's space slot holds after a step was that slot's
before it, or records no mapping.**  What a step that keeps no thread slot's
record it did not already hold reads. -/
def threadSlotsDrawnFrom (st st' : SystemState) : Prop :=
  ∀ (tid : SeLe4n.ObjId) (t' : TCB) (s : SeLe4n.Slot) (cap : Capability),
    st'.objects[tid]? = some (.tcb t') → t'.spaceSlotCap s = some cap →
      cap.mapping = none ∨ ∃ t, st.objects[tid]? = some (.tcb t) ∧ t.spaceSlotCap s = some cap

theorem threadSlotsRecordNoMapping.of_drawnFrom {st st' : SystemState}
    (hD : threadSlotsDrawnFrom st st') (h : st.threadSlotsRecordNoMapping) :
    st'.threadSlotsRecordNoMapping := fun tid t' s cap hT hC => by
  rcases hD tid t' s cap hT hC with hm | ⟨t, ht, hc⟩
  · exact hm
  · exact h tid t s cap ht hc

theorem threadSlotsDrawnFrom.refl (st : SystemState) : threadSlotsDrawnFrom st st :=
  fun _ t _ _ hT hC => .inr ⟨t, hT, hC⟩

theorem threadSlotsDrawnFrom.trans {s1 s2 s3 : SystemState} (hFirst : threadSlotsDrawnFrom s1 s2)
    (hSecond : threadSlotsDrawnFrom s2 s3) : threadSlotsDrawnFrom s1 s3 :=
  fun tid t3 s cap h3 hc3 => by
    rcases hSecond tid t3 s cap h3 hc3 with hm | ⟨t2, h2, hc2⟩
    · exact .inl hm
    · exact hFirst tid t2 s cap h2 hc2

/-- **A write of one key draws every thread slot from the pre-state** when every
other key keeps its object and a thread at the written key holds, in each slot,
what the key's thread held there before, or a capability recording nothing. -/
theorem threadSlotsDrawnFrom.of_key {st st' : SystemState} (k : SeLe4n.ObjId)
    (hNe : ∀ j : SeLe4n.ObjId, j ≠ k → st'.objects[j]? = st.objects[j]?)
    (hK : ∀ t', st'.objects[k]? = some (.tcb t') → ∀ (s : SeLe4n.Slot) (cap : Capability),
      t'.spaceSlotCap s = some cap →
        cap.mapping = none ∨ ∃ t, st.objects[k]? = some (.tcb t) ∧ t.spaceSlotCap s = some cap) :
    threadSlotsDrawnFrom st st' := fun tid t' s cap hT hC => by
  by_cases hj : tid = k
  · subst hj; exact hK t' hT s cap hC
  · rw [hNe tid hj] at hT; exact .inr ⟨t', hT, hC⟩

/-- **A step keeping every key's thread slots draws every thread slot from the
pre-state.** -/
theorem threadSlotsDrawnFrom.of_tcbSlots {st st' : SystemState}
    (hS : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).bind KernelObject.tcbSlots =
      (st.objects[k]?).bind KernelObject.tcbSlots) :
    threadSlotsDrawnFrom st st' := fun tid t' s cap hT hC => by
  right
  have e := hS tid
  rw [hT] at e
  cases ho : st.objects[tid]? with
  | none => rw [ho] at e; cases e
  | some o =>
    rw [ho] at e
    cases o with
    | tcb t =>
      simp only [Option.bind_some, KernelObject.tcbSlots, Option.some.injEq, Prod.mk.injEq] at e
      refine ⟨t, rfl, ?_⟩
      unfold TCB.spaceSlotCap at hC ⊢
      rw [← e.1]; exact hC
    | _ => cases e

/-- **A step under which every key agrees off its derivation links draws every
thread slot from the pre-state**: a thread differs at most in its link words. -/
theorem threadSlotsDrawnFrom.of_agreeOffLinks {st st' : SystemState}
    (hA : objectsAgreeOffDerivationLinks st' st) : threadSlotsDrawnFrom st st' :=
  fun tid t' s cap hT hC => by
    right
    rcases hA tid with e | ⟨cn, cn', -, h2, -⟩ | ⟨t, t'', h1, h2, hw⟩
    · exact ⟨t', e ▸ hT, hC⟩
    · rw [hT] at h2; cases h2
    · rw [hT] at h2; cases h2
      exact ⟨t, h1, by rw [← TCB.spaceSlotCap_withoutLinks, ← hw, TCB.spaceSlotCap_withoutLinks]; exact hC⟩

/-- **Every root after a step was a root before it with no more mappings**: the
same ASID, and no address mapped to a new entry or given a new epoch.  The
mapping half of `vspaceRootsShrink`. -/
def mappingRootsShrink (st st' : SystemState) : Prop :=
  ∀ (rid : SeLe4n.ObjId) (r' : VSpaceRoot), st'.objects[rid]? = some (.vspaceRoot r') →
    ∃ r : VSpaceRoot, st.objects[rid]? = some (.vspaceRoot r) ∧ r'.asid = r.asid ∧
      (∀ (v : SeLe4n.VAddr) (e : SeLe4n.PAddr × PagePermissions),
        r'.mappings[v]? = some e → r.mappings[v]? = some e) ∧
      (∀ (v : SeLe4n.VAddr) (n : Nat), r'.mappingEpochs[v]? = some n →
        r.mappingEpochs[v]? = some n)

theorem mappingRootsShrink.refl (st : SystemState) : mappingRootsShrink st st :=
  fun _ r' h => ⟨r', h, rfl, fun _ _ hm => hm, fun _ _ he => he⟩

theorem mappingRootsShrink.trans {s1 s2 s3 : SystemState} (hFirst : mappingRootsShrink s1 s2)
    (hSecond : mappingRootsShrink s2 s3) : mappingRootsShrink s1 s3 := fun rid r3 h3 => by
  obtain ⟨r2, h2, ha2, hm2, he2⟩ := hSecond rid r3 h3
  obtain ⟨r1, h1, ha1, hm1, he1⟩ := hFirst rid r2 h2
  exact ⟨r1, h1, ha2.trans ha1, fun v e hv => hm1 v e (hm2 v e hv),
    fun v n hv => he1 v n (he2 v n hv)⟩

/-- **A step keeps every record**: each mapping a slot records before it, a slot
records after it, to a frame with the same base. -/
def mappingRecordsKept (st st' : SystemState) : Prop :=
  ∀ (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (epoch : Nat),
    st.mappingRecordedAt asid vaddr paddr epoch → st'.mappingRecordedAt asid vaddr paddr epoch

theorem mappingRecordsKept.refl (st : SystemState) : mappingRecordsKept st st :=
  fun _ _ _ _ h => h

theorem mappingRecordsKept.trans {s1 s2 s3 : SystemState} (hFirst : mappingRecordsKept s1 s2)
    (hSecond : mappingRecordsKept s2 s3) : mappingRecordsKept s1 s3 :=
  fun a v p e h => hSecond a v p e (hFirst a v p e h)

/-- **A step whose roots only shrink and which keeps every record keeps every
live mapping witnessed.** -/
theorem liveMappingsWitnessed.of_shrink {st st' : SystemState} (hS : mappingRootsShrink st st')
    (hK : mappingRecordsKept st st') (h : st.liveMappingsWitnessed) :
    st'.liveMappingsWitnessed := by
  intro rid r' v p perms e hR hM hE
  obtain ⟨r, hr, ha, hm, he⟩ := hS rid r' hR
  rw [ha]
  exact hK _ _ _ _ (h rid r v p perms e hr (hm v _ hM) (he v e hE))

/-- **A step whose roots only shrink, which keeps every record and draws every
thread slot from the pre-state, keeps the mappings recorded.** -/
theorem liveMappingsRecorded.of_shrink {st st' : SystemState} (hS : mappingRootsShrink st st')
    (hK : mappingRecordsKept st st') (hT : threadSlotsDrawnFrom st st')
    (h : st.liveMappingsRecorded) : st'.liveMappingsRecorded :=
  ⟨h.1.of_shrink hS hK, h.2.of_drawnFrom hT⟩

/-- **A slot read and a frame read kept forward keep every record**: a step under
which every slot's capability that records a mapping is still held by some slot,
with its target and record, and every frame is still a frame with its base. -/
theorem mappingRecordsKept.of_fwd {st st' : SystemState}
    (hC : ∀ (r : SlotRef) (cap : Capability), st.slotCapAt r = some cap → cap.mapped = true →
      ∃ (r' : SlotRef) (cap' : Capability), st'.slotCapAt r' = some cap' ∧
        cap'.target = cap.target ∧ cap'.mapping = cap.mapping)
    (hF : ∀ (fid : SeLe4n.ObjId) (f : FrameObject), st.objects[fid]? = some (.frame f) →
      ∃ f' : FrameObject, st'.objects[fid]? = some (.frame f') ∧ f'.base = f.base) :
    mappingRecordsKept st st' := by
  rintro asid v p e ⟨r, cap, fid, f, hc, ht, hf, hb, hm⟩
  have hMapped : cap.mapped = true := by
    unfold Capability.mapping at hm
    split at hm
    · assumption
    · cases hm
  obtain ⟨r', cap', hc', ht', hm'⟩ := hC r cap hc hMapped
  obtain ⟨f', hf', hb'⟩ := hF fid f hf
  exact ⟨r', cap', fid, f', hc', ht'.trans ht, hf', hb'.trans hb, hm'.trans hm⟩

/-- A step that writes no object keeps the mappings recorded: they read the
objects alone. -/
theorem liveMappingsRecorded.of_objects_eq {st st' : SystemState} (hO : st'.objects = st.objects)
    (h : st.liveMappingsRecorded) : st'.liveMappingsRecorded := by
  have hC : ∀ r, st'.slotCapAt r = st.slotCapAt r := fun r => by
    rw [slotCapAt_eq_bind, slotCapAt_eq_bind, hO]
  refine ⟨fun rid root v p perms e hR hM hE => ?_, fun tid t s cap hT hc => ?_⟩
  · rw [hO] at hR
    obtain ⟨r, cap, fid, f, hc, ht, hf, hb, hm⟩ := h.1 rid root v p perms e hR hM hE
    exact ⟨r, cap, fid, f, (hC r).trans hc, ht, hO ▸ hf, hb, hm⟩
  · rw [hO] at hT; exact h.2 tid t s cap hT hc

/-- **A write of slot holders alone, keeping every record**: every key holds
what it held, or an object holding no mapping facts before and after (no root,
no frame: `KernelObject.mappingView` empty), and every capability recording a
mapping is still held by some slot with its target and record, and every thread
slot's capability was that slot's before, or records nothing.  What a
capability write is: the CNode or thread it writes holds slots, not mappings. -/
theorem liveMappingsRecorded.of_slotWrite {st st' : SystemState}
    (hObj : ∀ k : SeLe4n.ObjId, st'.objects[k]? = st.objects[k]? ∨
      ∃ pre post : KernelObject, st.objects[k]? = some pre ∧ st'.objects[k]? = some post ∧
        pre.mappingView = (none, none) ∧ post.mappingView = (none, none))
    (hSlot : ∀ (r : SlotRef) (cap : Capability), st.slotCapAt r = some cap → cap.mapped = true →
      ∃ (r' : SlotRef) (cap' : Capability), st'.slotCapAt r' = some cap' ∧
        cap'.target = cap.target ∧ cap'.mapping = cap.mapping)
    (hThreads : threadSlotsDrawnFrom st st')
    (h : st.liveMappingsRecorded) : st'.liveMappingsRecorded :=
  liveMappingsRecorded.of_shrink
    (fun rid r' hR => by
      rcases hObj rid with e | ⟨pre, post, -, hq, -, hv⟩
      · exact ⟨r', e ▸ hR, rfl, fun _ _ h => h, fun _ _ h => h⟩
      · rw [hR] at hq; cases hq; cases hv)
    (mappingRecordsKept.of_fwd hSlot fun fid f hf => by
      rcases hObj fid with e | ⟨pre, post, hp, -, hv, -⟩
      · exact ⟨f, e.trans hf, rfl⟩
      · rw [hf] at hp; cases hp; cases hv)
    hThreads h

/-- **A write of derivation links alone keeps the mappings recorded**: it
rewrites CNodes and threads in their link words only, so every slot reads as
before and no root or frame moves. -/
theorem liveMappingsRecorded.of_linkReach {st₀ st : SystemState} (hR : linkReach st₀ st)
    (hInv : st₀.objects.invExt) (h : st₀.liveMappingsRecorded) : st.liveMappingsRecorded := by
  have hF := SlotTreeFrame.of_linkReach hR hInv
  refine liveMappingsRecorded.of_slotWrite (fun k => ?_)
    (fun r cap hc _ => ⟨r, cap, (hF.slotCapAt r).trans hc, rfl, rfl⟩)
    (threadSlotsDrawnFrom.of_agreeOffLinks (hR.agree hInv)) h
  rcases hR.agree hInv k with e | ⟨cn, cn', h1, h2, -⟩ | ⟨t, t', h1, h2, -⟩
  · exact .inl e
  · exact .inr ⟨_, _, h1, h2, rfl, rfl⟩
  · exact .inr ⟨_, _, h1, h2, rfl, rfl⟩

/-- **A slot witnesses no live mapping**: no capability it holds records a
mapping an address space still makes under the record's epoch, to the frame the
capability targets.  What a step that overwrites or destroys the slot's record
reads: the record it loses witnessed nothing. -/
def slotWitnessesNoMapping (st : SystemState) (s : SlotRef) : Prop :=
  ∀ (cap : Capability) (fid : SeLe4n.ObjId) (f : FrameObject) (rid : SeLe4n.ObjId)
    (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) (perms : PagePermissions) (epoch : Nat),
    st.slotCapAt s = some cap → cap.target = .object fid → st.objects[fid]? = some (.frame f) →
    st.objects[rid]? = some (.vspaceRoot root) → root.mappings[vaddr]? = some (f.base, perms) →
    root.mappingEpochs[vaddr]? = some epoch →
    cap.mapping ≠ some { asid := root.asid, vaddr := vaddr, epoch := epoch }

/-- **A write of derivation links alone draws every thread slot from the
pre-state.** -/
theorem threadSlotsDrawnFrom.of_linkReach {st₀ st : SystemState} (hR : linkReach st₀ st)
    (hInv : st₀.objects.invExt) : threadSlotsDrawnFrom st₀ st :=
  threadSlotsDrawnFrom.of_agreeOffLinks (hR.agree hInv)

/-- **A thread's space slot witnesses no live mapping**, on a state no thread
slot of which records one. -/
theorem threadSlotsRecordNoMapping.slotWitnessesNoMapping {st : SystemState}
    (h : st.threadSlotsRecordNoMapping) {r : SlotRef} {t : TCB}
    (hT : st.objects[r.cnode]? = some (.tcb t)) : st.slotWitnessesNoMapping r := by
  intro cap fid f rid root v perms e hc _ _ _ _ _ hm
  rw [slotCapAt_eq_bind, hT] at hc
  rw [h r.cnode t r.slot cap hT hc] at hm
  cases hm

/-- **A step that adds at most one mapping, recorded, and rewrites at most one
slot, whose record witnessed nothing, keeps the mappings recorded.**  Every
mapping after the step is the new one (`asid`, `vaddr`, `paddr`, `epoch`), which
a slot records after it, or one an address space made before it under the same
ASID; every slot but `s` keeps its capability, every frame its base, the record `s`
held before the step witnessed no live mapping, and every thread slot's
capability was that slot's before, or records nothing. -/
theorem liveMappingsRecorded.of_step {st st' : SystemState} (s : SlotRef)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (epoch : Nat)
    (hRoots : ∀ (rid : SeLe4n.ObjId) (r' : VSpaceRoot) (v : SeLe4n.VAddr) (p : SeLe4n.PAddr)
      (perms : PagePermissions) (e : Nat), st'.objects[rid]? = some (.vspaceRoot r') →
      r'.mappings[v]? = some (p, perms) → r'.mappingEpochs[v]? = some e →
      (r'.asid = asid ∧ v = vaddr ∧ p = paddr ∧ e = epoch) ∨
      ∃ r : VSpaceRoot, st.objects[rid]? = some (.vspaceRoot r) ∧ r.asid = r'.asid ∧
        r.mappings[v]? = some (p, perms) ∧ r.mappingEpochs[v]? = some e)
    (hNew : st'.mappingRecordedAt asid vaddr paddr epoch)
    (hSlots : ∀ (r : SlotRef) (cap : Capability), r ≠ s → st.slotCapAt r = some cap →
      st'.slotCapAt r = some cap)
    (hFrames : ∀ (fid : SeLe4n.ObjId) (f : FrameObject), st.objects[fid]? = some (.frame f) →
      ∃ f' : FrameObject, st'.objects[fid]? = some (.frame f') ∧ f'.base = f.base)
    (hS : st.slotWitnessesNoMapping s) (hThreads : threadSlotsDrawnFrom st st')
    (h : st.liveMappingsRecorded) : st'.liveMappingsRecorded := by
  refine ⟨fun rid r' v p perms e hR hM hE => ?_, h.2.of_drawnFrom hThreads⟩
  rcases hRoots rid r' v p perms e hR hM hE with ⟨ha, hv, hp, he⟩ | ⟨r, hr, ha, hm, hep⟩
  · subst ha hv hp he; exact hNew
  · obtain ⟨w, cap, fid, f, hc, ht, hf, hb, hmap⟩ := h.1 rid r v p perms e hr hm hep
    by_cases hw : w = s
    · subst hw
      subst hb
      exact absurd hmap (hS cap fid f rid r v perms e hc ht hf hr hm hep)
    · obtain ⟨f', hf', hb'⟩ := hFrames fid f hf
      rw [← ha]
      exact ⟨w, cap, fid, f', hSlots w cap hw hc, ht, hf', hb'.trans hb, hmap⟩

end SystemState

/-- A post-state object of a frame's kind, holding a frame's mapping facts, is
that frame's base. -/
private theorem frame_of_kind_view {post : KernelObject} {f : FrameObject}
    (hT : post.objectType = (KernelObject.frame f).objectType)
    (hV : post.mappingView = (KernelObject.frame f).mappingView) :
    ∃ f', post = .frame f' ∧ f'.base = f.base := by
  cases post <;> simp [KernelObject.objectType, KernelObject.mappingView] at hT hV ⊢
  exact hV

/-- A post-state object of a root's kind, holding a root's mapping facts, is a
root with that ASID, those translations and those epochs. -/
private theorem root_of_kind_view {pre : KernelObject} {r' : VSpaceRoot}
    (hT : (KernelObject.vspaceRoot r').objectType = pre.objectType)
    (hV : (KernelObject.vspaceRoot r').mappingView = pre.mappingView) :
    ∃ r, pre = .vspaceRoot r ∧ r'.asid = r.asid ∧ r'.mappings = r.mappings ∧
      r'.mappingEpochs = r.mappingEpochs := by
  cases pre <;> simp [KernelObject.objectType, KernelObject.mappingView] at hT hV ⊢
  exact hV

/-- **A write that keeps every object's mapping facts**: at every key the store
is unchanged, or holds an object of the same kind, not a CNode, with the same
thread slots and the same mapping facts (`KernelObject.mappingView`).  Weaker
than `kindPreservingWrite`: it may move an object's untyped record, binding
codes and table back-links, none of which the mapping records read — the
notification bind and unbind move the binding codes. -/
def SystemState.mappingFactsKept (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ pre post : KernelObject,
      st.objects[oid]? = some pre ∧ st'.objects[oid]? = some post ∧
      post.objectType = pre.objectType ∧ post.objectType ≠ KernelObjectType.cnode ∧
      post.tcbSlots = pre.tcbSlots ∧ post.mappingView = pre.mappingView

namespace SystemState.mappingFactsKept

theorem refl (st : SystemState) : st.mappingFactsKept st := fun _ => .inl rfl

theorem trans {st st' st'' : SystemState} (h₁ : st.mappingFactsKept st')
    (h₂ : st'.mappingFactsKept st'') : st.mappingFactsKept st'' := fun oid => by
  rcases h₁ oid with e₁ | ⟨p₁, q₁, hp₁, hq₁, ht₁, hn₁, hs₁, hm₁⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hn₂, hs₂, hm₂⟩
    · exact .inl (e₂.trans e₁)
    · exact .inr ⟨p₂, q₂, e₁ ▸ hp₂, hq₂, ht₂, hn₂, hs₂, hm₂⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hn₂, hs₂, hm₂⟩
    · exact .inr ⟨p₁, q₁, hp₁, e₂.trans hq₁, ht₁, hn₁, hs₁, hm₁⟩
    · rw [hq₁] at hp₂; cases hp₂
      exact .inr ⟨p₁, q₂, hp₁, hq₂, ht₂.trans ht₁, hn₂, hs₂.trans hs₁, hm₂.trans hm₁⟩

end SystemState.mappingFactsKept

/-- A kind-preserving write keeps every object's mapping facts. -/
theorem kindPreservingWrite.mappingFactsKept {st st' : SystemState}
    (h : kindPreservingWrite st st') : st.mappingFactsKept st' := fun oid =>
  (h oid).imp id fun ⟨pre, post, hp, hq, ht, hn, hs, _, _, _, hm⟩ =>
    ⟨pre, post, hp, hq, ht, hn, hs, hm⟩

/-- One store of an object of the kind it replaces, not a CNode, with the
replaced object's thread slots and mapping facts. -/
theorem SystemState.mappingFactsKept_storeObject {st st' : SystemState} {oid : SeLe4n.ObjId}
    {obj pre : KernelObject} (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st')) (hPre : st.objects[oid]? = some pre)
    (hKind : obj.objectType = pre.objectType)
    (hNotCnode : obj.objectType ≠ KernelObjectType.cnode)
    (hSlots : obj.tcbSlots = pre.tcbSlots := by rfl)
    (hMapping : obj.mappingView = pre.mappingView := by rfl) :
    st.mappingFactsKept st' := fun k => by
  by_cases hEq : k = oid
  · subst hEq
    exact .inr ⟨pre, obj, hPre, storeObject_objects_eq st st' k obj hObjInv hStore, hKind,
      hNotCnode, hSlots, hMapping⟩
  · exact .inl (storeObject_objects_ne st st' oid k obj hEq hObjInv hStore)

/-- **A write that keeps every object's mapping facts keeps the mappings
recorded**: it writes no CNode, keeps every thread's slots, and keeps every
root's ASID, translations and epochs and every frame's base. -/
theorem SystemState.liveMappingsRecorded.of_mappingFactsKept {st st' : SystemState}
    (hK : st.mappingFactsKept st') (h : st.liveMappingsRecorded) :
    st'.liveMappingsRecorded := by
  refine SystemState.liveMappingsRecorded.of_shrink (fun rid r' hR => ?_)
    (SystemState.mappingRecordsKept.of_fwd (fun r cap hc _ => ?_) (fun fid f hf => ?_))
    (SystemState.threadSlotsDrawnFrom.of_tcbSlots fun k => ?_) h
  · rcases hK rid with e | ⟨pre, post, hp, hq, ht, -, -, hm⟩
    · exact ⟨r', e ▸ hR, rfl, fun _ _ h => h, fun _ _ h => h⟩
    · rw [hR] at hq; cases hq
      obtain ⟨r, rfl, ha, hmp, hep⟩ := root_of_kind_view ht hm
      exact ⟨r, hp, ha, fun v e h => hmp ▸ h, fun v n h => hep ▸ h⟩
  · rw [SystemState.slotCapAt_eq_bind] at hc
    cases ho : st.objects[r.cnode]? with
    | none => rw [ho] at hc; cases hc
    | some o =>
      rw [ho] at hc
      have hs : ∃ o', st'.objects[r.cnode]? = some o' ∧ o'.slotCap = o.slotCap := by
        rcases hK r.cnode with e | ⟨pre, post, hp, hq, ht, hn, hsl, -⟩
        · exact ⟨o, e.trans ho, rfl⟩
        · rw [ho] at hp; cases hp
          exact ⟨post, hq, (KernelObject.slots_eq_of_tcbSlots ht hn hsl).1⟩
      obtain ⟨o', ho', hs⟩ := hs
      refine ⟨r, cap, ?_, rfl, rfl⟩
      rw [SystemState.slotCapAt_eq_bind, ho']
      show o'.slotCap r.slot = some cap
      rw [hs]; exact hc
  · rcases hK fid with e | ⟨pre, post, hp, hq, ht, -, -, hm⟩
    · exact ⟨f, e ▸ hf, rfl⟩
    · rw [hf] at hp; cases hp
      obtain ⟨f', rfl, hb⟩ := frame_of_kind_view ht hm
      exact ⟨f', hq, hb⟩
  · rcases hK k with e | ⟨pre, post, hp, hq, -, -, hs, -⟩
    · rw [e]
    · rw [hp, hq]; exact hs

/-- **A kind-preserving write keeps the mappings recorded**
(`kindPreservingWrite.mappingFactsKept`).  Every IPC and scheduler step is one. -/
theorem SystemState.liveMappingsRecorded.of_kindPreservingWrite {st st' : SystemState}
    (hK : kindPreservingWrite st st') (h : st.liveMappingsRecorded) :
    st'.liveMappingsRecorded :=
  SystemState.liveMappingsRecorded.of_mappingFactsKept hK.mappingFactsKept h

/-- **An object stored at a key no object held keeps the mappings recorded**,
when it is no address space holding a mapping epoch and no thread whose space
slot records a mapping: every other key keeps its object, so every slot that
recorded a mapping keeps its capability and every frame it names stays (neither
is at the fresh key), and the new object adds no live mapping and no thread
slot's record.  What a carve's store of its child is. -/
theorem SystemState.liveMappingsRecorded.of_freshObject {st st' : SystemState} {k : SeLe4n.ObjId}
    {obj : KernelObject} (hFresh : st.objects[k]? = none) (hK : st'.objects[k]? = some obj)
    (hNe : ∀ j, j ≠ k → st'.objects[j]? = st.objects[j]?)
    (hNoEpoch : ∀ root, obj = .vspaceRoot root → ∀ (v : SeLe4n.VAddr) (e : Nat),
      root.mappingEpochs[v]? = some e → False)
    (hNoRecord : ∀ t, obj = .tcb t → ∀ (s : SeLe4n.Slot) (cap : Capability),
      t.spaceSlotCap s = some cap → cap.mapping = none)
    (h : st.liveMappingsRecorded) : st'.liveMappingsRecorded := by
  refine ⟨fun rid root v p perms e hR hM hE => ?_, fun tid t s cap hT hc => ?_⟩
  rotate_left
  · by_cases hr : tid = k
    · subst hr; rw [hK] at hT; cases hT; exact hNoRecord t rfl s cap hc
    · rw [hNe tid hr] at hT; exact h.2 tid t s cap hT hc
  by_cases hr : rid = k
  · subst hr; rw [hK] at hR; cases hR; exact absurd hE (fun hE => hNoEpoch root rfl v e hE)
  · rw [hNe rid hr] at hR
    obtain ⟨r, cap, fid, f, hc, ht, hf, hb, hm⟩ := h.1 rid root v p perms e hR hM hE
    have hcK : r.cnode ≠ k := by
      intro hx; rw [SystemState.slotCapAt_eq_bind, hx, hFresh] at hc; cases hc
    have hfK : fid ≠ k := by intro hx; rw [hx, hFresh] at hf; cases hf
    refine ⟨r, cap, fid, f, ?_, ht, (hNe fid hfK).trans hf, hb, hm⟩
    rw [SystemState.slotCapAt_eq_bind, hNe r.cnode hcK, ← SystemState.slotCapAt_eq_bind]
    exact hc

/-- **A state in which no root holds a mapping epoch, and no thread slot a
record, records every mapping**, the first vacuously: no mapping was made by a
capability.  What the boot leaves, every root's epoch table vacant
(`RHTable.vacant`) and every thread slot's capability passing
`bootSafeCapCheck`. -/
theorem SystemState.liveMappingsRecorded_of_epochsVacant {st : SystemState}
    (h : ∀ (rid : SeLe4n.ObjId) (root : VSpaceRoot), st.objects[rid]? = some (.vspaceRoot root) →
      root.mappingEpochs.vacant = true)
    (hThreads : st.threadSlotsRecordNoMapping) :
    st.liveMappingsRecorded := by
  refine ⟨fun rid root v p perms e hR _ hE => ?_, hThreads⟩
  have hV := h rid root hR
  have hK := RHTable.vacant_invExtK _ hV
  have hSize : root.mappingEpochs.size = 0 := by
    unfold RHTable.vacant at hV
    simp only [Bool.and_eq_true, beq_iff_eq] at hV
    exact hV.1.2
  rw [RHTable_getElem?_eq_get?, RHTable.get?_none_of_size_zero _ hK.1 hSize] at hE
  cases hE

/-- The empty state records every mapping: it holds no root and no thread. -/
theorem SystemState.default_liveMappingsRecorded : (default : SystemState).liveMappingsRecorded :=
  SystemState.liveMappingsRecorded_of_epochsVacant
    (fun rid root h => by
      rw [show (default : SystemState).objects[rid]? = none from RHTable_get?_empty 16 (by omega)] at h
      cases h)
    fun tid t s cap h => by
      rw [show (default : SystemState).objects[tid]? = none from RHTable_get?_empty 16 (by omega)] at h
      cases h

end SeLe4n.Model
