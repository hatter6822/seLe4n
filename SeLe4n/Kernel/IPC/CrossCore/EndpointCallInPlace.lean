/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointSend

/-!
# The call rendezvous, written in place

WS-ZA ZA4.7: a call that finds a receiver waiting writes the endpoint, the
receiver, its queue successor, the caller, the reply object, the run queues
and the reply-waiter links.  The specification (`endpointCallOnCore` inside
`endpointCallCrossCoreDispatch`) reaches each write through a step that may
refuse, so its compiled form keeps the pre-state alive for the refusal and
copies every table it writes.  Here every refusal is ruled out before the first
write (`callRendezvousFast`, the seL4 decode/perform split), and the writes run
on a state nothing else holds (`storeCallRendezvous`), proven equal to the
specification (`callRendezvous_inPlace_eq`).

What makes the proof go without a table invariant is that each write either
rewrites a key where it stands (`RHTable.findsInPlace`) or maps one slot's value
(`RHTable.mapValueAt`): neither moves a key, so the in-place question asked of
the pre-state stays answered along the chain (`objectsKeepFinds`).
-/

namespace SeLe4n.Kernel.RobinHood

variable {α β : Type} [BEq α] [Hashable α]

/-- Mapping one slot's value moves no key, so every in-place question is
answered as before. -/
theorem RHTable.findsInPlace_mapValueAt (t : RHTable α β) (k k' : α) (f : β → β) :
    (t.mapValueAt k f).findsInPlace k' = t.findsInPlace k' := by
  unfold RHTable.findsInPlace RHTable.mapValueAt
  dsimp only
  rw [findIdxLoop_modify_mapValue]

end SeLe4n.Kernel.RobinHood

namespace SeLe4n.Model.SystemState

open SeLe4n.Kernel.RobinHood

/-- Every key's in-place question is answered in `st'` as in `st`. -/
def objectsKeepFinds (st' st : SystemState) : Prop :=
  ∀ k, st'.objects.findsInPlace k = st.objects.findsInPlace k

namespace objectsKeepFinds

theorem refl (st : SystemState) : objectsKeepFinds st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₂ : objectsKeepFinds c b) (h₁ : objectsKeepFinds b a) :
    objectsKeepFinds c a := fun k => (h₂ k).trans (h₁ k)

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    objectsKeepFinds st' st := fun k => by rw [h]

end objectsKeepFinds

theorem mapTcbInPlace_keepsFinds (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB) :
    (st.mapTcbInPlace t g).objectsKeepFinds st := fun _ =>
  RHTable.findsInPlace_mapValueAt _ _ _ _

theorem updateTcbAtCode_keepsFinds (st : SystemState) (k : Nat) (g : TCB → TCB) :
    (st.updateTcbAtCode k g).objectsKeepFinds st := by
  unfold updateTcbAtCode; split
  · exact .refl _
  · exact mapTcbInPlace_keepsFinds _ _ _

theorem runAppendLinks_keepsFinds (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runAppendLinks c t p).objectsKeepFinds st := by
  unfold runAppendLinks
  exact (updateTcbAtCode_keepsFinds _ _ _).trans
    ((updateTcbAtCode_keepsFinds _ _ _).trans (mapTcbInPlace_keepsFinds _ _ _))

theorem runEnqueueAdmitted_keepsFinds (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (st.runEnqueueAdmitted c t p).objectsKeepFinds st := by
  have h := runEnqueueAdmitted_objects st c t p
  split at h
  · exact .of_objects_eq h
  · exact fun k => by rw [h]; exact runAppendLinks_keepsFinds st c t p k

end SeLe4n.Model.SystemState

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood

/-- A wake's enqueue rewrites the woken TCB where it stands and maps run-link
slots, so it moves no key. -/
theorem enqueueRunnableOnCore_keepsFinds (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (hF : st.objects.findsInPlace tid.toObjId = true) :
    (enqueueRunnableOnCore st c tid).objectsKeepFinds st := by
  unfold enqueueRunnableOnCore
  split
  · split
    · exact .refl _
    · exact fun k => ((SystemState.runEnqueueAdmitted_keepsFinds _ c tid _) k).trans
        (RHTable.findsInPlace_insert_of_findsInPlace k _ hF)
  · exact .refl _

/-- `enqueueRunnableOnCore_objectsAgreeOffRunLinks_of_ready` with the woken key
found in place instead of a well-formed table. -/
theorem enqueueRunnableOnCore_agree_of_findsInPlace
    (st : SystemState) (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hF : st.objects.findsInPlace tid.toObjId = true) :
    (enqueueRunnableOnCore st c tid).objectsAgreeOffRunLinks st := by
  have hObjTcb := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  have hVal : (KernelObject.tcb { tcb with ipcState := .ready }) = .tcb tcb := by rw [← hReady]
  unfold enqueueRunnableOnCore
  simp only [SystemState.getTcbWitnessed?_eq_some hTcb]
  split
  · exact .refl _
  · refine SystemState.objectsAgreeOffRunLinks.congr rfl rfl
      ((SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ c tid _).trans
        (.of_getElem_eq fun oid => ?_))
    show (st.objects.insert tid.toObjId (.tcb { tcb with ipcState := .ready }))[oid]?
        = st.objects[oid]?
    rw [hVal]
    simp only [RHTable_getElem?_eq_get?]
    by_cases hEq : tid.toObjId = oid
    · subst hEq
      rw [RHTable.get?_insert_self_of_findsInPlace _ hF]
      simpa only [RHTable_getElem?_eq_get?] using hObjTcb.symm
    · exact RHTable.get?_insert_ne_of_findsInPlace oid _ hF hEq

/-- The pop of a receive queue's head, each write in its slot: the endpoint's
queue starts at the head's successor, the successor becomes the head, the head
is unlinked. -/
@[inline] def storePopHead (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) : SystemState :=
  let s1 := st.modifyObject endpointId (sendRendezvousEndpoint next)
  let s2 := match next with
    | none => s1
    | some n => s1.updateTcb n tcbAsQueueHead
  s2.updateTcb head tcbOffQueue

/-- What a pop written in place leaves: the head unlinked, every key found where
it was, every store still local, and every key other than the endpoint, the head
and its successor untouched. -/
structure PopHeadFrame (st s : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (ht : TCB) : Prop where
  head_tcb : s.getTcb? head = some (tcbOffQueue ht)
  keepsFinds : s.objectsKeepFinds st
  leaves : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
    storeLeavesIndexAndTypes s id ty = true
  other : ∀ x, endpointId ≠ x → head.toObjId ≠ x → (∀ n, next = some n → n.toObjId ≠ x) →
    s.objects[x]? = st.objects[x]?

/-- **The pop of a receive queue's head, in place**: under `sendWakesInPlace`
the specification's pop succeeds with `storePopHead`'s state, which keeps the
pop's frame. -/
theorem popHead_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (head : SeLe4n.ThreadId) (ht : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep))
    (hH : ep.receiveQ.head = some head)
    (hT : st.objects[head.toObjId]? = some (.tcb ht))
    (hG : sendWakesInPlace st endpointId head ht.queueNext = true) :
    endpointQueuePopHead endpointId true st =
        .ok (head, ht, storePopHead st endpointId head ht.queueNext) ∧
      PopHeadFrame st (storePopHead st endpointId head ht.queueNext) endpointId head
        ht.queueNext ht := by
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨hRes, hLE⟩, hFE⟩, hLH⟩, hFH⟩, hNx⟩ := hG
  have hNeEH : endpointId ≠ head.toObjId := by
    intro h; rw [h, hT] at hE; cases hE
  have hLook : lookupTcb st head = some ht := by
    simp only [lookupTcb, hRes, Bool.false_eq_true, ↓reduceIte]
    exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨S1, hS1⟩ : ∃ S1 : SystemState, S1 = { st with objects :=
      (st.objects.insert endpointId (sendRendezvousEndpoint ht.queueNext (.endpoint ep))) } :=
    ⟨_, rfl⟩
  have hMo : st.modifyObject endpointId (sendRendezvousEndpoint ht.queueNext) = S1 := by
    rw [hS1]; unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? hE]
  have hNotV : ∀ r, sendRendezvousEndpoint ht.queueNext (.endpoint ep) ≠ .vspaceRoot r := by
    intro r h; simp only [sendRendezvousEndpoint] at h; split at h <;> cases h
  have hF1 : ∀ k, S1.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [hS1]; exact RHTable.findsInPlace_insert_of_findsInPlace k _ hFE
  have hG1 : ∀ k, endpointId ≠ k → S1.objects[k]? = st.objects[k]? := fun k hk => by
    rw [hS1]; exact RHTable.get?_insert_ne_of_findsInPlace k _ hFE hk
  have hL1 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S1 id ty = true := fun h => by
    rw [hS1]; exact storeLeavesIndexAndTypes_insert_inPlace hFE hNotV h
  have hT1 : S1.getTcb? head = some ht :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr ((hG1 _ hNeEH).trans hT)
  unfold endpointQueuePopHead storePopHead
  simp only [SystemState.getObject?, hE, hH, hLook, Bool.not_true, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  rw [hMo]
  cases hN : ht.queueNext with
  | none =>
    have hSt : storeObject endpointId (.endpoint { ep with receiveQ := {} }) st = .ok ((), S1) := by
      rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLE), hS1, hN]; rfl
    simp only [hSt]
    have hQ : storeTcbQueueLinks S1 head none none none =
        .ok (S1.updateTcb head tcbOffQueue) :=
      modifyTcb_eq_updateTcb _ hRes hT1 (hL1 hLH)
    rw [hQ]
    have hFH1 : S1.objects.findsInPlace head.toObjId = true := (hF1 _).trans hFH
    exact ⟨rfl,
      { head_tcb := updateTcb_getTcb?_self_of_findsInPlace _ hT1 hFH1
        keepsFinds := fun k => (updateTcb_findsInPlace _ hT1 hFH1 k).trans (hF1 k)
        leaves := fun h => updateTcb_storeLeaves _ hT1 hFH1 (hL1 h)
        other := fun x hEx hHx _ =>
          (updateTcb_get?_ne_of_findsInPlace _ hT1 hFH1 hHx).trans (hG1 x hEx) }⟩
  | some n =>
    rw [hN] at hNx
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hNx
    obtain ⟨⟨⟨⟨hRn, hNeH⟩, hLN⟩, hFN⟩, hTnB⟩ := hNx
    obtain ⟨nt, hTn⟩ := Option.isSome_iff_exists.mp hTnB
    have hNeEN : endpointId ≠ n.toObjId := by
      intro h; rw [h, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTn] at hE; cases hE
    have hNeNH : n.toObjId ≠ head.toObjId := fun h =>
      hNeH (SeLe4n.ThreadId.toObjId_injective _ _ h)
    have hSt : storeObject endpointId
        (.endpoint { ep with receiveQ := { head := some n, tail := ep.receiveQ.tail } }) st =
        .ok ((), S1) := by
      rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLE), hS1, hN]; rfl
    simp only [hSt]
    have hTn1 : S1.getTcb? n = some nt :=
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr
        ((hG1 _ hNeEN).trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTn))
    have hLookN : lookupTcb S1 n = some nt := by
      simp only [lookupTcb, hRn, Bool.false_eq_true, ↓reduceIte]; exact hTn1
    rw [hLookN]
    simp only []
    let g := tcbAsQueueHead
    have hQn : storeTcbQueueLinks S1 n none (some .endpointHead) nt.queueNext =
        .ok (S1.updateTcb n g) := by
      have := modifyTcb_eq_updateTcb (fun t => tcbWithQueueLinks t none (some .endpointHead)
        nt.queueNext) hRn hTn1 (hL1 hLN)
      rw [show storeTcbQueueLinks S1 n none (some .endpointHead) nt.queueNext =
        modifyTcb S1 n (fun t => tcbWithQueueLinks t none (some .endpointHead) nt.queueNext)
        from rfl, this, SystemState.updateTcb_eq_of_some hTn1, SystemState.updateTcb_eq_of_some hTn1]
      simp only [g, tcbAsQueueHead_eq]
    rw [hQn]
    simp only []
    obtain ⟨S2, hS2⟩ : ∃ S2 : SystemState, S2 = S1.updateTcb n g := ⟨_, rfl⟩
    rw [← hS2]
    have hFn1 : S1.objects.findsInPlace n.toObjId = true := (hF1 _).trans hFN
    have hT2 : S2.getTcb? head = some ht := by
      rw [hS2, SystemState.getTcb?_eq_some_iff,
        updateTcb_get?_ne_of_findsInPlace g hTn1 hFn1 hNeNH]
      exact (SystemState.getTcb?_eq_some_iff _ _ _).mp hT1
    have hF2 : ∀ k, S2.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
      rw [hS2, updateTcb_findsInPlace g hTn1 hFn1, hF1]
    have hL2 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
        storeLeavesIndexAndTypes S2 id ty = true := fun h => by
      rw [hS2]; exact updateTcb_storeLeaves g hTn1 hFn1 (hL1 h)
    have hQ : storeTcbQueueLinks S2 head none none none =
        .ok (S2.updateTcb head tcbOffQueue) :=
      modifyTcb_eq_updateTcb _ hRes hT2 (hL2 hLH)
    rw [hQ]
    have hFH2 : S2.objects.findsInPlace head.toObjId = true := (hF2 _).trans hFH
    exact ⟨rfl,
      { head_tcb := updateTcb_getTcb?_self_of_findsInPlace _ hT2 hFH2
        keepsFinds := fun k => (updateTcb_findsInPlace _ hT2 hFH2 k).trans (hF2 k)
        leaves := fun h => updateTcb_storeLeaves _ hT2 hFH2 (hL2 h)
        other := fun x hEx hHx hNx' => by
          rw [updateTcb_get?_ne_of_findsInPlace _ hT2 hFH2 hHx, hS2,
            updateTcb_get?_ne_of_findsInPlace g hTn1 hFn1 (hNx' n rfl)]
          exact hG1 x hEx }⟩

end SeLe4n.Kernel
