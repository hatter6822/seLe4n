-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.SetSpace
import SeLe4n.Kernel.MappingRecordStage.Retype

/-!
# The carve keeps the records

WS-ZA ZA6.37.  A carve writes its untyped's watermark, stores its child at an
id no object held, sets the authority capability's free index, scrubs the
child's memory, inserts the child's capability and records the derivation
edge.  Only the child's store adds an object: a carved thread is unlinked from
every reply-waiter queue and carries no fault (`ReplyViews.consistent_of_added`),
and a carved address space has an ASID the table does not hold and no
translation (`teardownWellFormed_storeFreshRoot`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The queues stay consistent when an unlinked view is added** at a slot that
held none: no queue reaches it and no waiter names it, since its server would
have needed a view. -/
theorem ReplyViews.consistent_of_added {V V' : ReplyViews}
    (h : ∀ k, V' k = V k ∨ (V k = none ∧ V' k = some ReplyView.idle))
    (hc : V.consistent) : V'.consistent := by
  have hBack : ∀ k v, V k = some v → V' k = some v := fun k v hv => by
    rcases h k with e | ⟨hn, -⟩
    · rw [e]; exact hv
    · rw [hn] at hv; cases hv
  have hWait : ∀ w s, V'.waiterOf w s ↔ V.waiterOf w s := fun w s => by
    refine ⟨fun ⟨v, hv, hs⟩ => ?_, fun ⟨v, hv, hs⟩ => ⟨v, hBack _ _ hv, hs⟩⟩
    rcases h w.toObjId with e | ⟨-, hi⟩
    · exact ⟨v, e ▸ hv, hs⟩
    · rw [hi] at hv; cases hv; cases hs
  have hChain : ∀ (l : List ThreadId) (p c : Option ThreadId), V.chain p c l → V'.chain p c l := by
    intro l
    induction l with
    | nil => intro p c hc'; exact hc'
    | cons w l ih =>
      intro p c hc'
      obtain ⟨hcur, v, hv, hp, hrest⟩ := hc'
      exact ⟨hcur, v, hBack _ _ hv, hp, ih _ _ hrest⟩
  refine ⟨fun s vs hs => ?_, fun w vw s hw hs => ?_, fun w vw hw hn => ?_, fun w vw hw => ?_⟩
  · rcases h s.toObjId with e | ⟨hn, hi⟩
    · obtain ⟨l, hCh, hLen, hNd, hMem⟩ := hc.1 s vs (e ▸ hs)
      exact ⟨l, hChain l _ _ hCh, hLen, hNd, fun w => (hMem w).trans (hWait w s).symm⟩
    · rw [hi] at hs; cases hs
      refine ⟨[], rfl, rfl, List.nodup_nil, fun w => ⟨fun hm => absurd hm List.not_mem_nil, ?_⟩⟩
      intro hW
      obtain ⟨v, hv, hsv⟩ := (hWait w s).mp hW
      obtain ⟨vs, hvs⟩ := hc.2.1 w v s hv hsv
      rw [hn] at hvs; cases hvs
  · rcases h w.toObjId with e | ⟨-, hi⟩
    · obtain ⟨vs, hvs⟩ := hc.2.1 w vw s (e ▸ hw) hs
      exact ⟨vs, hBack _ _ hvs⟩
    · rw [hi] at hw; cases hw; cases hs
  · rcases h w.toObjId with e | ⟨-, hi⟩
    · exact hc.2.2.1 w vw (e ▸ hw) hn
    · rw [hi] at hw; cases hw; exact ⟨rfl, rfl⟩
  · rcases h w.toObjId with e | ⟨-, hi⟩
    · exact hc.2.2.2 w vw (e ▸ hw)
    · rw [hi] at hw; cases hw; intro hs; cases hs

/-- **A new address space stored at an id no object held, under an ASID the
table does not hold and with no translation, keeps the state well formed.** -/
theorem teardownWellFormed_storeFreshRoot {st st' : SystemState} {k : SeLe4n.ObjId}
    {r : VSpaceRoot} (hT : teardownWellFormed st) (hNone : st.objects[k]? = none)
    (hFresh : st.asidTable[r.asid]? = none)
    (hEmpty : ∀ v : SeLe4n.VAddr, r.mappings[v]? = none)
    (hWF : r.mappings.invExtK ∧ r.mappingEpochs.invExtK)
    (hS : storeObject k (.vspaceRoot r) st = .ok ((), st')) : teardownWellFormed st' := by
  obtain ⟨hI, hAK, hB⟩ := hT
  have hEq : st'.objects[k]? = some (.vspaceRoot r) := storeObject_objects_eq st st' _ _ hI hS
  have hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' k oid _ h hI hS
  have hA : st'.asidTable = st.asidTable.insert r.asid k := by
    unfold storeObject at hS; cases hS
    have hk : storeKeepsAsid st k (.vspaceRoot r) = false := by simp [storeKeepsAsid, hNone]
    simp only [hk, hNone, Bool.false_eq_true, ↓reduceIte]
  have hLkSelf : st'.asidTable[r.asid]? = some k := by
    rw [hA]; simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_self _ _ _ hAK.1
  have hLkNe : ∀ a : SeLe4n.ASID, a ≠ r.asid → st'.asidTable[a]? = st.asidTable[a]? := fun a h => by
    rw [hA]; simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => h (eq_of_beq hb).symm) hAK.1
  have hOld : ∀ (oid : SeLe4n.ObjId) (q : VSpaceRoot), st.objects[oid]? = some (.vspaceRoot q) → q.asid ≠ r.asid :=
    fun oid q hq he => by
      have := hB.2.2.1.2 oid q hq
      rw [he, hFresh] at this; cases this
  have hBack : ∀ (oid : SeLe4n.ObjId) (q : VSpaceRoot), st'.objects[oid]? = some (.vspaceRoot q) →
      (oid = k ∧ q = r) ∨ (oid ≠ k ∧ st.objects[oid]? = some (.vspaceRoot q)) := fun oid q h => by
    by_cases hk : oid = k
    · subst hk; rw [hEq] at h; cases h; exact .inl ⟨rfl, rfl⟩
    · rw [hNe oid hk] at h; exact .inr ⟨hk, h⟩
  have hMapBack : ∀ (oid : SeLe4n.ObjId) (q : VSpaceRoot) (v : SeLe4n.VAddr) (e : SeLe4n.PAddr × PagePermissions),
      st'.objects[oid]? = some (.vspaceRoot q) → q.mappings[v]? = some e →
        st.objects[oid]? = some (.vspaceRoot q) := fun oid q v e h hm => by
    rcases hBack oid q h with ⟨-, rfl⟩ | ⟨-, h0⟩
    · rw [hEmpty v] at hm; cases hm
    · exact h0
  refine ⟨storeObject_preserves_objects_invExt st st' _ _ hI hS,
    by rw [hA]; exact RobinHood.RHTable.insert_preserves_invExtK _ _ _ hAK, ?_⟩
  unfold Architecture.vspaceInvariantBundle Architecture.vspaceAsidRootsUnique
    Architecture.vspaceRootNonOverlap Architecture.asidTableConsistent
    Architecture.wxExclusiveInvariant Architecture.boundedAddressTranslation
    Architecture.vspaceCrossAsidIsolation Architecture.canonicalAddressInvariant
    Architecture.vspaceMappingsWellFormed at hB ⊢
  obtain ⟨c1, -, ⟨c3a, c3b⟩, c4, c5, c6, c7, c8⟩ := hB
  refine ⟨?_, fun o q _ => VSpaceRoot.noVirtualOverlap_trivial q, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro o1 o2 r1 r2 h1 h2 he
    rcases hBack o1 r1 h1 with ⟨rfl, rfl⟩ | ⟨-, h1'⟩ <;>
      rcases hBack o2 r2 h2 with ⟨rfl, rfl⟩ | ⟨-, h2'⟩
    · rfl
    · exact absurd he.symm (hOld _ _ h2')
    · exact absurd he (hOld _ _ h1')
    · exact c1 o1 o2 r1 r2 h1' h2' he
  · intro a o hL
    by_cases ha : a = r.asid
    · subst ha; rw [hLkSelf] at hL; cases hL; exact ⟨r, hEq, rfl⟩
    · rw [hLkNe a ha] at hL
      obtain ⟨q, hq, hqa⟩ := c3a a o hL
      have hok : o ≠ k := fun e => by rw [e, hNone] at hq; cases hq
      exact ⟨q, (hNe o hok).trans hq, hqa⟩
  · intro o q h
    rcases hBack o q h with ⟨rfl, rfl⟩ | ⟨-, h0⟩
    · exact hLkSelf
    · rw [hLkNe _ (hOld _ _ h0)]; exact c3b o q h0
  · intro o q v p pm h hm; exact c4 o q v p pm (hMapBack o q v _ h hm) hm
  · intro o q v p pm h hm; exact c5 o q v p pm (hMapBack o q v _ h hm) hm
  · intro o1 o2 r1 r2 h1 h2 hne
    rcases hBack o1 r1 h1 with ⟨rfl, rfl⟩ | ⟨-, h1'⟩ <;>
      rcases hBack o2 r2 h2 with ⟨rfl, rfl⟩ | ⟨-, h2'⟩
    · exact absurd rfl hne
    · exact fun he => hOld _ _ h2' he.symm
    · exact hOld _ _ h1'
    · exact c6 o1 o2 r1 r2 h1' h2' hne
  · intro o q v p pm h hm; exact c7 o q v p pm (hMapBack o q v _ h hm) hm
  · intro o q h
    rcases hBack o q h with ⟨-, rfl⟩ | ⟨-, h0⟩
    · exact hWF
    · exact c8 o q h0

/-- The scrub writes memory, not the machine's address width. -/
theorem CarveRequest.scrub_physicalAddressWidth (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) :
    (req.scrub st ut idx).machine.physicalAddressWidth = st.machine.physicalAddressWidth := by
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

/-- The scrub writes no ASID. -/
theorem CarveRequest.scrub_asidTable (st : SystemState) (ut : UntypedObject) (idx : Nat)
    (req : CarveRequest) : (req.scrub st ut idx).asidTable = st.asidTable := by
  cases req <;> simp only [CarveRequest.scrub, carveZeroFrame] <;> (try split) <;> rfl

namespace RecordsStage

/-- **An object stored at an id no object held**: a thread unlinked and
carrying no fault, an address space under a free ASID with no translation, or
an object no record reads. -/
theorem storeFresh {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hNone : st.objects[k]? = none)
    (hTcb : ∀ t, o = .tcb t → t.replyView = ReplyView.idle ∧ t.pendingFault = none)
    (hRoot : ∀ r, o = .vspaceRoot r → st.asidTable[r.asid]? = none ∧
      (∀ v : SeLe4n.VAddr, r.mappings[v]? = none) ∧ r.mappings.invExtK ∧ r.mappingEpochs.invExtK)
    (hS : storeObject k o st = .ok ((), st')) : RecordsStage st st' := by
  intro hK
  have hI := KernelRecords.objects_invExt hK
  have hEq : st'.objects[k]? = some o := storeObject_objects_eq st st' _ _ hI hS
  have hNe : ∀ oid, oid ≠ k → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' k oid _ h hI hS
  have hT' : teardownWellFormed st' := by
    by_cases hR : ∃ r, o = .vspaceRoot r
    · obtain ⟨r, rfl⟩ := hR
      obtain ⟨hA, hM, hW1, hW2⟩ := hRoot r rfl
      exact teardownWellFormed_storeFreshRoot hK.1 hNone hA hM ⟨hW1, hW2⟩ hS
    · have hNR : ∀ r, o ≠ .vspaceRoot r := fun r e => hR ⟨r, e⟩
      refine teardownWellFormed_of_roots_eq (storeObject_preserves_objects_invExt _ _ _ _ hI hS)
        ?_ (fun oid r => ?_) hK.1
      · rw [storeObject_asidTable_non_vspaceRoot st st' k o hNR hS, hNone]
      · by_cases hk : oid = k
        · subst hk
          rw [hEq, hNone]
          exact ⟨fun e => absurd (Option.some.inj e) (hNR r), fun e => by cases e⟩
        · rw [hNe oid hk]
  have hRV : ∀ x, st'.replyViews x = st.replyViews x ∨
      (st.replyViews x = none ∧ st'.replyViews x = some ReplyView.idle) := fun x => by
    by_cases hk : x = k
    · subst hk
      unfold SystemState.replyViews SystemState.getObject?
      rw [hEq, hNone]
      cases o with
      | tcb t => exact .inr ⟨rfl, by rw [objReplyView_tcb, (hTcb t rfl).1]⟩
      | _ => exact .inl rfl
    · left
      unfold SystemState.replyViews SystemState.getObject?
      rw [hNe x hk]
  refine ⟨hT', ReplyViews.consistent_of_added hRV hK.2.1, ?_,
    hK.2.2.2.of_eq (by rw [storeObject_machine_eq st st' _ _ hS])⟩
  refine FaultsStayParked.preserves (fun t tcb' hT hF H => ?_) hK.2.2.1
  have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  by_cases hk : t.toObjId = k
  · rw [hk, hEq] at hO
    cases hO
    rw [(hTcb tcb' rfl).2] at hF; cases hF
  · rw [hNe _ hk] at hO
    exact H tcb' ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO) hF

end RecordsStage

namespace RecordsStage

/-- **The carve keeps the records**: the watermark, the fresh child, the free
index, the scrub, the capability insert and the derivation edge. -/
theorem untypedRetypeObject {src dst : CSpaceAddr} {childId : SeLe4n.ObjId}
    {req : CarveRequest} {st st' : SystemState}
    (h : _root_.SeLe4n.Kernel.untypedRetypeObject src childId dst req st = .ok ((), st')) :
    RecordsStage st st' := by
  intro hK
  have hInv := KernelRecords.objects_invExt hK
  have hAdm := untypedRetypeObject_ok_admissible src dst childId req st st' h
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hInv h
  have hFresh := retypeFromUntyped_childId_fresh src untypedId childId _ _ st st1 hRt
  obtain ⟨ut₀, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, hLk, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st1 src untypedId childId _ _ hInv hRt
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hChildNone : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hInv hStUt]
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have hAUt : stUt.asidTable = st.asidTable := by
    rw [storeObject_asidTable_non_vspaceRoot st stUt untypedId _ (fun _ => by simp) hStUt, hUt]
  have k1 := (RecordsFrame.storeObject hInv hStUt (by rw [hUt]; rfl) (fun _ => by simp)).preserves hK
  have k2 := storeFresh (hS := hStCh) hChildNone
    (fun t ht => by
      cases req <;> simp only [CarveRequest.object, KernelObject.tcb.injEq, reduceCtorEq] at ht
      subst ht; exact ⟨rfl, rfl⟩)
    (fun r hr => by
      cases req <;> simp only [CarveRequest.object, KernelObject.vspaceRoot.injEq,
        reduceCtorEq] at hr
      subst hr
      simp only [CarveRequest.admissible, Bool.and_eq_true, Option.isNone_iff_eq_none] at hAdm
      refine ⟨by rw [hAUt]; exact hAdm.2, fun v => ?_, RobinHood.RHTable.empty_invExtK 16 (by omega),
        RobinHood.RHTable.empty_invExtK 16 (by omega)⟩
      simp only [RHTable_getElem?_eq_get?]
      exact RobinHood.RHTable.getElem?_empty _ _ v) k1
  have k3 := (RecordsFrame.storeObject (KernelRecords.objects_invExt k2) hStIdx (by rw [hOCh]; rfl)
    (fun _ => by simp)).preserves k2
  have k4 := (RecordsFrame.of_objects_eq (KernelRecords.objects_invExt k3)
    (CarveRequest.scrub_objects st1 ut _ req) (CarveRequest.scrub_asidTable st1 ut _ req)
    (CarveRequest.scrub_physicalAddressWidth st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))
      req)).preserves k3
  have k5 := (RecordsFrame.cspaceInsertSlot (KernelRecords.objects_invExt k4) hIns).preserves k4
  exact (RecordsFrame.cdtAddChild st2 _ _ _ (KernelRecords.objects_invExt k5)).preserves k5

/-- The live `.untypedRetype` arm: the carve. -/
theorem untypedRetypeFromCap {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId}
    {srcAddr : SeLe4n.CPtr}
    {args? : Except KernelError SeLe4n.Kernel.Architecture.SyscallArgDecode.UntypedRetypeArgs}
    {st st' : SystemState}
    (h : _root_.SeLe4n.Kernel.untypedRetypeFromCap tid ec srcAddr args? st = .ok ((), st')) :
    RecordsStage st st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hCarve⟩ := untypedRetypeFromCap_ok tid ec srcAddr args? st st' h
  exact untypedRetypeObject hCarve

end RecordsStage

end SeLe4n.Kernel
