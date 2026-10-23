/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.DualQueue.Core

/-!
# An endpoint queue's head popped in place

WS-ZA ZA4.7: the pop of an endpoint queue's head (`endpointQueuePopHead`),
written as one rewrite of each object it touches where that object stands
(`storePopHead`), and proven equal to the specification's pop whenever every
store stays in its slot (`sendWakesInPlace`, `popHead_inPlace`).  The send, the
call and the receive rendezvous each pop a head this way, and so does the final
delete's cancellation of an endpoint's waiters, which is why the pop sits below
all of them rather than inside the send.

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

end SeLe4n.Model.SystemState

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood

/-- WS-ZA ZA4.7: the endpoint a pop leaves: its receive queue
(`isReceiveQ`) or its send queue starts at the popped head's successor, given
as its code (`SeLe4n.ThreadId.optCode`), so a caller holding the successor's
link code passes it without building an `Option`. -/
@[inline] def popEndpoint (isReceiveQ : Bool) (nextCode : Nat) :
    KernelObject → KernelObject
  | .endpoint e =>
      -- the queue ends are codes in the endpoint, rewritten in its cell
      -- (`Endpoint.withReceiveQ_head`, `Endpoint.withSendQ_head`)
      match isReceiveQ, nextCode with
      | true, 0 => .endpoint { e with recvHeadCode := 0, recvTailCode := 0 }
      | true, c + 1 => .endpoint { e with recvHeadCode := c + 1 }
      | false, 0 => .endpoint { e with sendHeadCode := 0, sendTailCode := 0 }
      | false, c + 1 => .endpoint { e with sendHeadCode := c + 1 }
  | o => o

/-- WS-ZA ZA4.7: a thread taken off an endpoint queue: its three link codes
cleared (`tcbWithQueueLinks t none none none` by definition). -/
@[inline] def tcbOffQueue (t : TCB) : TCB :=
  { t with queuePrevCode := 0, queuePPrevCode := 0, queueNextCode := 0 }

/-- WS-ZA ZA4.7: a queue's new head: no predecessor, its back-pointer the
queue head, as codes (`tcbAsQueueHead_eq`). -/
@[inline] def tcbAsQueueHead (t : TCB) : TCB :=
  { t with queuePrevCode := 0, queuePPrevCode := 1 }

theorem tcbAsQueueHead_eq (t : TCB) :
    tcbAsQueueHead t = tcbWithQueueLinks t none (some .endpointHead) t.queueNext := by
  simp only [tcbAsQueueHead, tcbWithQueueLinks, TCB.optCode_queueNext]
  rfl

/-- WS-ZA ZA4.7: **the send rendezvous writes only its slots** — the endpoint,
the popped receiver and its successor each rewritten where it stands
(`RHTable.findsInPlace`), each store changing only `objects`
(`storeLeavesIndexAndTypes`), the receiver and its successor distinct,
unreserved TCBs. -/
@[inline] def sendWakesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) : Bool :=
  !head.isReserved &&
  storeLeavesIndexAndTypes st endpointId .endpoint &&
  st.objects.findsInPlace endpointId &&
  storeLeavesIndexAndTypes st head.toObjId .tcb &&
  st.objects.findsInPlace head.toObjId &&
  (match next with
   | none => true
   | some n => !n.isReserved && n != head &&
       storeLeavesIndexAndTypes st n.toObjId .tcb &&
       st.objects.findsInPlace n.toObjId &&
       (st.getTcb? n).isSome)

/-- The pop of an endpoint queue's head (the receive queue when
`isReceiveQ`, else the send queue), each write in its slot: the endpoint's
queue starts at the head's successor, the successor becomes the head, the head
is unlinked. -/
@[inline] def storePopHead (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) : SystemState :=
  let s1 := st.modifyObject endpointId (popEndpoint isReceiveQ (ThreadId.optCode next))
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

/-- **The pop of an endpoint queue's head, in place**: under
`sendWakesInPlace` the specification's pop succeeds with `storePopHead`'s
state, which keeps the pop's frame. -/
theorem popHead_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (ep : Endpoint) (head : SeLe4n.ThreadId) (ht : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep))
    (hH : (if isReceiveQ then ep.receiveQ else ep.sendQ).head = some head)
    (hT : st.objects[head.toObjId]? = some (.tcb ht))
    (hG : sendWakesInPlace st endpointId head ht.queueNext = true) :
    endpointQueuePopHead endpointId isReceiveQ st =
        .ok (head, ht, storePopHead st endpointId isReceiveQ head ht.queueNext) ∧
      PopHeadFrame st (storePopHead st endpointId isReceiveQ head ht.queueNext) endpointId head
        ht.queueNext ht := by
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨hRes, hLE⟩, hFE⟩, hLH⟩, hFH⟩, hNx⟩ := hG
  have hNeEH : endpointId ≠ head.toObjId := by
    intro h; rw [h, hT] at hE; cases hE
  have hLook : lookupTcb st head = some ht := by
    simp only [lookupTcb, hRes, Bool.false_eq_true, ↓reduceIte]
    exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨S1, hS1⟩ : ∃ S1 : SystemState, S1 = { st with objects :=
      (st.objects.insert endpointId
        (popEndpoint isReceiveQ (ThreadId.optCode ht.queueNext) (.endpoint ep))) } :=
    ⟨_, rfl⟩
  have hMo : st.modifyObject endpointId
      (popEndpoint isReceiveQ (ThreadId.optCode ht.queueNext)) = S1 := by
    rw [hS1]; unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? hE]
  have hNotV : ∀ r, popEndpoint isReceiveQ (ThreadId.optCode ht.queueNext) (.endpoint ep) ≠
      .vspaceRoot r := by
    intro r h; simp only [popEndpoint] at h; split at h <;> cases h
  have hLE' : ∀ e : Endpoint, storeLeavesIndexAndTypes st endpointId
      (KernelObject.endpoint e).objectType = true := fun _ => by
    simpa only [KernelObject.objectType] using hLE
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
    have hSt : storeObject endpointId (.endpoint (if isReceiveQ then ep.withReceiveQ {}
        else ep.withSendQ {})) st = .ok ((), S1) := by
      rw [storeObject_eq_of_leaves (hLE' _), hS1, hN]; cases isReceiveQ <;> rfl
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
        (.endpoint (if isReceiveQ then
          ep.withReceiveQ ⟨some n, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩
          else ep.withSendQ ⟨some n, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩))
        st = .ok ((), S1) := by
      rw [storeObject_eq_of_leaves (hLE' _), hS1, hN]
      cases isReceiveQ
      · simp only [Bool.false_eq_true, ↓reduceIte, Endpoint.withSendQ_head]; rfl
      · simp only [↓reduceIte, Endpoint.withReceiveQ_head]; rfl
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
