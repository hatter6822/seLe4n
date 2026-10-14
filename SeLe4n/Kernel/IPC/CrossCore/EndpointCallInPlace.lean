/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointSend
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch

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
  let s1 := st.modifyObject endpointId (sendRendezvousEndpoint (ThreadId.optCode next))
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
      (st.objects.insert endpointId
        (sendRendezvousEndpoint (ThreadId.optCode ht.queueNext) (.endpoint ep))) } :=
    ⟨_, rfl⟩
  have hMo : st.modifyObject endpointId (sendRendezvousEndpoint (ThreadId.optCode ht.queueNext)) =
      S1 := by
    rw [hS1]; unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? hE]
  have hNotV : ∀ r, sendRendezvousEndpoint (ThreadId.optCode ht.queueNext) (.endpoint ep) ≠
      .vspaceRoot r := by
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
    have hSt : storeObject endpointId (.endpoint (ep.withReceiveQ {})) st = .ok ((), S1) := by
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
        (.endpoint (ep.withReceiveQ { head := some n, tail := ep.receiveQ.tail })) st =
        .ok ((), S1) := by
      rw [Endpoint.withReceiveQ_head, storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hLE), hS1, hN]; rfl
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

/-- A write that keeps the index and the lifecycle and holds every object up to
run links keeps every store local. -/
theorem storeLeaves_of_agree {s s' : SystemState}
    (hI : s'.objectIndexSet = s.objectIndexSet) (hL : s'.lifecycle = s.lifecycle)
    (hA : s'.objectsAgreeOffRunLinks s) {id : SeLe4n.ObjId} {ty : KernelObjectType}
    (h : storeLeavesIndexAndTypes s id ty = true) :
    storeLeavesIndexAndTypes s' id ty = true := by
  unfold storeLeavesIndexAndTypes at h ⊢
  rw [hI, hL]
  rcases hA.pointwise id with e | ⟨t, t', e, e'⟩
  · rw [e]; exact h
  · rw [e'] ; rw [e] at h; exact h

theorem storeLeaves_of_onlyObjectsSchedulerDiffer {s s' : SystemState}
    (hD : s'.onlyObjectsSchedulerDiffer s) (hA : s'.objectsAgreeOffRunLinks s)
    {id : SeLe4n.ObjId} {ty : KernelObjectType}
    (h : storeLeavesIndexAndTypes s id ty = true) :
    storeLeavesIndexAndTypes s' id ty = true :=
  storeLeaves_of_agree (by rw [hD]) (by rw [hD]) hA h

theorem runUnlinkLinks_keepsFinds (st : SystemState) (t : SeLe4n.ThreadId)
    (pv nx bpv bnx : Nat) : (st.runUnlinkLinks t pv nx bpv bnx).objectsKeepFinds st := by
  unfold SystemState.runUnlinkLinks
  exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans
    ((SystemState.updateTcbAtCode_keepsFinds _ _ _).trans
    ((SystemState.updateTcbAtCode_keepsFinds _ _ _).trans
    ((SystemState.updateTcbAtCode_keepsFinds _ _ _).trans
    (SystemState.updateTcbAtCode_keepsFinds _ _ _))))

/-- The dequeue rewrites run links where they stand, so it moves no key. -/
theorem removeRunnableOnCore_keepsFinds (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : Concurrency.CoreId) : (removeRunnableOnCore st tid c).objectsKeepFinds st := by
  intro k
  show (st.runRemoveOnCore c tid).objects.findsInPlace k = _
  rw [SystemState.runRemoveOnCore_objects]
  split
  · exact runUnlinkLinks_keepsFinds st tid _ _ _ _ k
  · rfl

/-- Joining a reply-waiter queue maps three slots' values, so it moves no key. -/
theorem linkReplyWaiter_keepsFinds (st : SystemState) (w s : SeLe4n.ThreadId) :
    (st.linkReplyWaiter w s).objectsKeepFinds st := by
  unfold SystemState.linkReplyWaiter
  exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans
    ((SystemState.updateTcbAtCode_keepsFinds _ _ _).trans
    (SystemState.mapTcbInPlace_keepsFinds _ _ _))

/-- The SchedContext a call donates, read off the two bindings alone. -/
def donationOfBindings : Option SchedContextBinding → Option SchedContextBinding →
    Option SeLe4n.SchedContextId
  | some .unbound, some b => b.scId?
  | _, _ => none

theorem callDonationSchedContext?_eq_bindings (st : SystemState) (c r : SeLe4n.ThreadId) :
    callDonationSchedContext? st c r =
      donationOfBindings ((lookupTcb st r).map TCB.schedContextBinding)
        ((lookupTcb st c).map TCB.schedContextBinding) := by
  unfold callDonationSchedContext?
  cases lookupTcb st r with
  | none => rfl
  | some rt =>
    cases hb : rt.schedContextBinding <;> cases lookupTcb st c <;>
      simp only [hb, Option.map_some, Option.map_none, donationOfBindings]

/-- Two states whose two threads hold the same bindings agree on the donation. -/
theorem callDonationSchedContext?_congr {s s' : SystemState} {c r : SeLe4n.ThreadId}
    (hc : (s'.getTcb? c).map TCB.schedContextBinding = (s.getTcb? c).map TCB.schedContextBinding)
    (hr : (s'.getTcb? r).map TCB.schedContextBinding = (s.getTcb? r).map TCB.schedContextBinding) :
    callDonationSchedContext? s' c r = callDonationSchedContext? s c r := by
  have hl : ∀ x, (s'.getTcb? x).map TCB.schedContextBinding =
      (s.getTcb? x).map TCB.schedContextBinding →
      (lookupTcb s' x).map TCB.schedContextBinding =
        (lookupTcb s x).map TCB.schedContextBinding := fun x h => by
    unfold lookupTcb; split
    · rfl
    · exact h
  rw [callDonationSchedContext?_eq_bindings, callDonationSchedContext?_eq_bindings,
    hl c hc, hl r hr]

/-- The donation guard on the two TCBs: a call donates only to an unbound
receiver from a caller holding a SchedContext. -/
@[inline] def callDonatesNothing (ct rt : TCB) : Bool :=
  match rt.schedContextBinding with
  | .unbound => match ct.schedContextBinding with
    | .unbound => true
    | _ => false
  | _ => true

/-- The reply object a call links its caller into. -/
@[inline] def replyWithCaller (caller : SeLe4n.ThreadId) : KernelObject → KernelObject
  | .reply r => .reply { r with caller := some caller }
  | o => o

/-- The receiver a call wakes: ready, holding the message. -/
@[inline] def callReceiverTcb (msg : IpcMessage) (t : TCB) : TCB :=
  { t with ipcState := .ready, pendingMessage := some msg }

/-- The caller a call blocks: waiting on the receiver's reply. -/
@[inline] def callCallerTcb (endpointId : SeLe4n.ObjId) (r : SeLe4n.ThreadId) (t : TCB) : TCB :=
  { t with ipcState := .blockedOnReply endpointId (some r), pendingMessage := none }

/-- **The call rendezvous writes only its slots**: the send rendezvous's slots
(`sendWakesInPlace`), the caller and the reply object each rewritten where they
stand, each store changing only `objects`, the caller a third unreserved thread
holding no reply object, the reply object free, and no SchedContext donated. -/
@[inline] def callWakesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (rt : TCB) (rid : SeLe4n.ReplyId) : Bool :=
  sendWakesInPlace st endpointId r rt.queueNext &&
  !caller.isReserved && caller != r &&
  (match rt.queueNext with
   | none => true
   | some n => caller != n) &&
  storeLeavesIndexAndTypes st caller.toObjId .tcb &&
  st.objects.findsInPlace caller.toObjId &&
  storeLeavesIndexAndTypes st rid.toObjId .reply &&
  st.objects.findsInPlace rid.toObjId &&
  (match st.getTcb? caller with
   | some ct => ct.replyObject.isNone && callDonatesNothing ct rt
   | none => false) &&
  (match st.getReply? rid with
   | some rp => rp.isFree
   | none => false)

/-- The call rendezvous's writes up to the priority walk, each in its slot: the
receiver popped and handed the message, woken on its home core; the caller
blocked on its reply, linked to the reply object the receiver stashed, taken off
its core and queued on the receiver's reply waiters. -/
@[noinline] def storeCallRendezvous (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (msg : IpcMessage) (core : Concurrency.CoreId) : SystemState :=
  let s2 := (storePopHead st endpointId r next).updateTcb r (callReceiverTcb msg)
  let s3 := enqueueRunnableOnCore s2 (determineTargetCore s2 r) r
  let s5 := (s3.updateTcb caller (callCallerTcb endpointId r)).modifyObject rid.toObjId
    (replyWithCaller caller)
  let s7 := (s5.updateTcb caller (fun t => { t with replyObject := some rid })).updateTcb r
    (fun t => { t with pendingReceiveReply := none })
  (removeRunnableOnCore s7 caller core).linkReplyWaiter caller r

/-- **The call rendezvous, in place**: under `callWakesInPlace` the
specification's call returns `storeCallRendezvous`'s state with the receiver
wake's SGI, and that state donates nothing. -/
theorem callRendezvous_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId) (ep : Endpoint)
    (caller r : SeLe4n.ThreadId) (rt : TCB) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (core : Concurrency.CoreId)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hCp : ¬ msg.caps.size > maxExtraCaps)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt)) (hRid : rt.pendingReceiveReply = some rid)
    (hG : callWakesInPlace st endpointId caller r rt rid = true) :
    endpointCallOnCore endpointId caller msg core st =
        (storeCallRendezvous st endpointId caller r rt.queueNext rid msg core,
         .ok (wakeThread ((storePopHead st endpointId r rt.queueNext).updateTcb r
           (callReceiverTcb msg)) r core).2) ∧
      callDonationSchedContext?
        (storeCallRendezvous st endpointId caller r rt.queueNext rid msg core) caller r = none := by
  simp only [callWakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hCRes⟩, hCR⟩, hCN⟩, hLC⟩, hFC⟩, hLR⟩, hFR⟩, hCT⟩, hRp⟩ := hG
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hRRes, hLE⟩, hFE⟩, hLH⟩, hFH⟩, hNx⟩ := hSG'
  obtain ⟨ct, hCo, hRO, hDN⟩ : ∃ ct, st.objects[caller.toObjId]? = some (.tcb ct) ∧
      ct.replyObject = none ∧ callDonatesNothing ct rt = true := by
    split at hCT
    · next ct hCo =>
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hCT
      exact ⟨ct, (SystemState.getTcb?_eq_some_iff _ _ _).mp hCo, hCT.1, hCT.2⟩
    · cases hCT
  obtain ⟨rp, hRo, hFree⟩ : ∃ rp, st.objects[rid.toObjId]? = some (.reply rp) ∧
      rp.isFree = true := by
    split at hRp
    · next rp hRo => exact ⟨rp, (SystemState.getReply?_eq_some_iff _ _ _).mp hRo, hRp⟩
    · cases hRp
  have hNk : ∀ n, rt.queueNext = some n →
      caller ≠ n ∧ ∃ nt, st.objects[n.toObjId]? = some (.tcb nt) := by
    intro n hn
    rw [hn] at hNx hCN
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hNx hCN
    obtain ⟨_, hTnB⟩ := hNx
    obtain ⟨nt, hTn⟩ := Option.isSome_iff_exists.mp hTnB
    exact ⟨hCN, nt, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTn⟩
  -- Distinct keys, from distinct kinds or distinct threads.
  have hNeEC : endpointId ≠ caller.toObjId := fun h => by rw [h, hCo] at hE; cases hE
  have hNeRC : r.toObjId ≠ caller.toObjId := fun h =>
    hCR (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNeCR : caller.toObjId ≠ r.toObjId := fun h => hNeRC h.symm
  have hNeEQ : endpointId ≠ rid.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeRQ : r.toObjId ≠ rid.toObjId := fun h => by rw [h, hRo] at hT; cases hT
  have hNeCQ : caller.toObjId ≠ rid.toObjId := fun h => by rw [h, hRo] at hCo; cases hCo
  have hNeQC : rid.toObjId ≠ caller.toObjId := fun h => hNeCQ h.symm
  have hNeQR : rid.toObjId ≠ r.toObjId := fun h => hNeRQ h.symm
  have hNxC : ∀ n, rt.queueNext = some n → n.toObjId ≠ caller.toObjId := fun n hn h =>
    (hNk n hn).1 (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxQ : ∀ n, rt.queueNext = some n → n.toObjId ≠ rid.toObjId := fun n hn h => by
    obtain ⟨_, nt, hTn⟩ := hNk n hn
    rw [h, hRo] at hTn; cases hTn
  unfold storeCallRendezvous
  dsimp only
  -- The pop.
  obtain ⟨hPop, hFr⟩ := popHead_inPlace st endpointId ep r rt hE hH hT hSG
  have hFH1 : (storePopHead st endpointId r rt.queueNext).objects.findsInPlace r.toObjId = true :=
    (hFr.keepsFinds _).trans hFH
  have hO1c := (hFr.other _ hNeEC hNeRC hNxC).trans hCo
  have hO1q := (hFr.other _ hNeEQ hNeRQ hNxQ).trans hRo
  -- The receiver handed the message.
  have hM2 : storeTcbIpcStateAndMessage (storePopHead st endpointId r rt.queueNext) r .ready
      (some msg) = .ok ((storePopHead st endpointId r rt.queueNext).updateTcb r
        (callReceiverTcb msg)) :=
    modifyTcb_eq_updateTcb (callReceiverTcb msg) hRRes hFr.head_tcb (hFr.leaves hLH)
  generalize hS1 : storePopHead st endpointId r rt.queueNext = S1 at *
  have hT2r := updateTcb_getTcb?_self_of_findsInPlace (callReceiverTcb msg) hFr.head_tcb hFH1
  have hO2c := (updateTcb_get?_ne_of_findsInPlace (callReceiverTcb msg) hFr.head_tcb hFH1
    hNeRC).trans hO1c
  have hO2q := (updateTcb_get?_ne_of_findsInPlace (callReceiverTcb msg) hFr.head_tcb hFH1
    hNeRQ).trans hO1q
  have hK2 : ∀ k, (S1.updateTcb r (callReceiverTcb msg)).objects.findsInPlace k =
      st.objects.findsInPlace k := fun k =>
    (updateTcb_findsInPlace _ hFr.head_tcb hFH1 k).trans (hFr.keepsFinds k)
  have hL2 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (S1.updateTcb r (callReceiverTcb msg)) id ty = true :=
    fun h => updateTcb_storeLeaves _ hFr.head_tcb hFH1 (hFr.leaves h)
  generalize hS2 : S1.updateTcb r (callReceiverTcb msg) = S2 at *
  -- The wake.
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace S2 (determineTargetCore S2 r) r _ hT2r
    rfl ((hK2 _).trans hFH)
  have hD3 := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer S2 (determineTargetCore S2 r) r
  have hK3 : ∀ k, (enqueueRunnableOnCore S2 (determineTargetCore S2 r) r).objects.findsInPlace k
      = st.objects.findsInPlace k := fun k =>
    (enqueueRunnableOnCore_keepsFinds S2 _ r ((hK2 _).trans hFH) k).trans (hK2 k)
  have hL3 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (enqueueRunnableOnCore S2 (determineTargetCore S2 r) r) id ty
        = true := fun h => storeLeaves_of_onlyObjectsSchedulerDiffer hD3 hA3 (hL2 h)
  obtain ⟨ct3, hO3c, hct3⟩ := hA3.get_tcb hO2c
  obtain ⟨rt3, hO3r, hrt3⟩ := hA3.get_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT2r)
  have hO3q := hA3.get_reply_iff.mpr hO2q
  have hW : (wakeThread S2 r core).1 = enqueueRunnableOnCore S2 (determineTargetCore S2 r) r := rfl
  generalize hS3 : enqueueRunnableOnCore S2 (determineTargetCore S2 r) r = S3 at *
  -- The caller blocked.
  have hT3c : S3.getTcb? caller = some ct3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3c
  have hFC3 := (hK3 _).trans hFC
  have hM4 : storeTcbIpcStateAndMessage S3 caller (.blockedOnReply endpointId (some r)) none =
      .ok (S3.updateTcb caller (callCallerTcb endpointId r)) :=
    modifyTcb_eq_updateTcb (callCallerTcb endpointId r) hCRes hT3c (hL3 hLC)
  have hT4r : (S3.updateTcb caller (callCallerTcb endpointId r)).getTcb? r = some rt3 :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      ((updateTcb_get?_ne_of_findsInPlace _ hT3c hFC3 hNeCR).trans hO3r)
  have hT4c := updateTcb_getTcb?_self_of_findsInPlace (callCallerTcb endpointId r) hT3c hFC3
  have hO4q := (updateTcb_get?_ne_of_findsInPlace (callCallerTcb endpointId r) hT3c hFC3
    hNeCQ).trans hO3q
  have hK4 : ∀ k, (S3.updateTcb caller (callCallerTcb endpointId r)).objects.findsInPlace k =
      st.objects.findsInPlace k := fun k =>
    (updateTcb_findsInPlace _ hT3c hFC3 k).trans (hK3 k)
  have hL4 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (S3.updateTcb caller (callCallerTcb endpointId r)) id ty = true :=
    fun h => updateTcb_storeLeaves _ hT3c hFC3 (hL3 h)
  generalize hS4 : S3.updateTcb caller (callCallerTcb endpointId r) = S4 at *
  -- The reply object linked.
  have hrt3rid : rt3.pendingReceiveReply = some rid := by
    have h := congrArg TCB.pendingReceiveReply hrt3; exact h.trans hRid
  have hct3RO : ct3.replyObject = none := by
    have h := congrArg TCB.replyObject hct3; exact h.trans hRO
  have hFR4 := (hK4 _).trans hFR
  have hS5 : S4.modifyObject rid.toObjId (replyWithCaller caller) =
      { S4 with objects := (S4.objects.insert rid.toObjId
          (.reply { rp with caller := some caller })) } := by
    unfold SystemState.modifyObject
    rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? (by exact hO4q)]
    rfl
  have hStR : storeObject rid.toObjId (.reply { rp with caller := some caller }) S4 =
      .ok ((), { S4 with objects := (S4.objects.insert rid.toObjId
          (.reply { rp with caller := some caller })) }) :=
    storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL4 hLR)
  rw [hS5]
  generalize hS5' : ({ S4 with objects := (S4.objects.insert rid.toObjId
      (.reply { rp with caller := some caller })) } : SystemState) = S5 at *
  have hO5 : ∀ k, rid.toObjId ≠ k → S5.objects[k]? = S4.objects[k]? := fun k hk => by
    rw [← hS5']; exact RHTable.get?_insert_ne_of_findsInPlace k _ hFR4 hk
  have hK5 : ∀ k, S5.objects.findsInPlace k = st.objects.findsInPlace k := fun k => by
    rw [← hS5']; exact (RHTable.findsInPlace_insert_of_findsInPlace k _ hFR4).trans (hK4 k)
  have hL5 : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes S5 id ty = true := fun h => by
    rw [← hS5']; exact storeLeavesIndexAndTypes_insert_inPlace hFR4 (fun _ e => by cases e) (hL4 h)
  have hT5c : S5.getTcb? caller = some (callCallerTcb endpointId r ct3) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      ((hO5 _ hNeQC).trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT4c))
  have hT5r : S5.getTcb? r = some rt3 :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      ((hO5 _ hNeQR).trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT4r))
  have hFC5 := (hK5 _).trans hFC
  have hFR5 := (hK5 _).trans hFH
  have hSt6 : storeObject caller.toObjId
      (.tcb { callCallerTcb endpointId r ct3 with replyObject := some rid }) S5 =
      .ok ((), S5.updateTcb caller (fun t => { t with replyObject := some rid })) := by
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL5 hLC),
      SystemState.updateTcb_eq_of_some hT5c]
  have hT6r : (S5.updateTcb caller (fun t => { t with replyObject := some rid })).getTcb? r =
      some rt3 :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      ((updateTcb_get?_ne_of_findsInPlace _ hT5c hFC5 hNeCR).trans
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT5r))
  have hSt7 : storeObject r.toObjId (.tcb { rt3 with pendingReceiveReply := none })
      (S5.updateTcb caller (fun t => { t with replyObject := some rid })) =
      .ok ((), (S5.updateTcb caller (fun t => { t with replyObject := some rid })).updateTcb r
        (fun t => { t with pendingReceiveReply := none })) := by
    have hL6 := updateTcb_storeLeaves (fun t => { t with replyObject := some rid }) hT5c hFC5
      (hL5 hLH)
    rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL6),
      SystemState.updateTcb_eq_of_some hT6r]
  have hRO5 : (callCallerTcb endpointId r ct3).replyObject.isNone = true := by
    simp only [callCallerTcb, hct3RO, Option.isNone_none]
  have hEp : st.getEndpoint? endpointId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
  have hRp4 : S4.getReply? rid = some rp := (SystemState.getReply?_eq_some_iff _ _ _).mpr hO4q
  refine ⟨?_, ?_⟩
  · unfold endpointCallOnCore
    rw [if_neg hSz, if_neg hCp, hEp]
    dsimp only
    rw [hH]
    dsimp only
    rw [hPop]
    dsimp only
    rw [hM2]
    dsimp only
    rw [hW, hM4]
    dsimp only
    unfold SystemState.linkServerStashedReply SystemState.linkCallerReply SystemState.linkReply
    simp only [hT4r, Option.bind_some, hrt3rid, hRp4, hFree, ↓reduceIte, hStR, hT5c, hRO5, hSt6,
      hT6r, hSt7]
  · have hT6c := updateTcb_getTcb?_self_of_findsInPlace
      (fun t => { t with replyObject := some rid }) hT5c hFC5
    have hFR6 := (updateTcb_findsInPlace (fun t => { t with replyObject := some rid }) hT5c hFC5
      r.toObjId).trans hFR5
    generalize hS6 : S5.updateTcb caller (fun t => { t with replyObject := some rid }) = S6 at *
    have hT7c : (S6.updateTcb r (fun t => { t with pendingReceiveReply := none })).getTcb? caller
        = some { callCallerTcb endpointId r ct3 with replyObject := some rid } :=
      (SystemState.getTcb?_eq_some_iff _ _ _).mpr
        ((updateTcb_get?_ne_of_findsInPlace _ hT6r hFR6 hNeRC).trans
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT6c))
    have hT7r := updateTcb_getTcb?_self_of_findsInPlace
      (fun t => { t with pendingReceiveReply := none }) hT6r hFR6
    generalize hS7 : S6.updateTcb r (fun t => { t with pendingReceiveReply := none }) = S7 at *
    have hA8 := (SystemState.linkReplyWaiter_objectsAgreeOffRunLinks
      (removeRunnableOnCore S7 caller core) caller r).trans
      (removeRunnableOnCore_objectsAgreeOffRunLinks S7 caller core)
    have hb3 : ct3.schedContextBinding = ct.schedContextBinding := by
      have h := congrArg TCB.schedContextBinding hct3; exact h
    have hbr3 : rt3.schedContextBinding = rt.schedContextBinding := by
      have h := congrArg TCB.schedContextBinding hrt3; exact h
    have hTc : st.getTcb? caller = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hCo
    have hTr : st.getTcb? r = some rt := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
    rw [callDonationSchedContext?_congr (s := st)
      ((TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.schedContextBinding
        (hA8.getTcb? caller)).trans (by rw [hT7c, hTc]; exact congrArg some hb3))
      ((TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.schedContextBinding
        (hA8.getTcb? r)).trans (by rw [hT7r, hTr]; exact congrArg some hbr3))]
    rw [callDonationSchedContext?_eq_bindings]
    simp only [lookupTcb, hRRes, hCRes, Bool.false_eq_true, ↓reduceIte, hTr, hTc, Option.map_some]
    revert hDN
    unfold callDonatesNothing
    cases rt.schedContextBinding <;> cases ct.schedContextBinding <;>
      simp [donationOfBindings, SchedContextBinding.scId?]

/-- The call rendezvous's state after the receiver's priority walk: what the
call dispatch commits on a rendezvous that donates nothing. -/
@[noinline] def performCallRendezvous (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (msg : IpcMessage) (core : Concurrency.CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore
    (storeCallRendezvous st endpointId caller r next rid msg core) r core).1

/-- **The checked call dispatch, in place**: under the flow gate and
`callWakesInPlace`, a capability-free call that finds a receiver commits
`performCallRendezvous`'s state with an empty transfer summary. -/
theorem callDispatchChecked_inPlace (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (caller r : SeLe4n.ThreadId) (rt : TCB)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (rights : AccessRightSet) (slot : SeLe4n.Slot)
    (core : Concurrency.CoreId)
    (hCaps : msg.caps = #[]) (hGrant : msg.capsGranted = rights.mem .grant)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt)) (hRid : rt.pendingReceiveReply = some rid)
    (hG : callWakesInPlace st endpointId caller r rt rid = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true) :
    ∃ sgi, endpointCallCrossCoreDispatchChecked ctx endpointId caller msg rights slot core st =
      (performCallRendezvous st endpointId caller r rt.queueNext rid msg core,
       .ok ({ results := #[] }, sgi)) := by
  have hG' := hG
  simp only [callWakesInPlace, sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
  have hCRes : caller.isReserved = false := hG'.1.1.1.1.1.1.1.1.2
  have hRRes : r.isReserved = false := hG'.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  have hEp : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
  have hStamp : { msg with capsGranted := rights.mem .grant } = msg := by
    rw [← hGrant]
  obtain ⟨hEq, hDon⟩ := callRendezvous_inPlace st endpointId ep caller r rt rid msg core hSz
    (by rw [hCaps]; decide) hE hH hT hRid hG
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff caller).mpr hCRes)
  obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff r).mpr hRRes)
  have hcv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv
  have hrv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hrv
  refine ⟨(wakeThread ((storePopHead st endpointId r rt.queueNext).updateTcb r
    (callReceiverTcb msg)) r core).2, ?_⟩
  unfold endpointCallCrossCoreDispatchChecked
  rw [if_pos hFlow]
  unfold endpointCallCrossCoreDispatch
  rw [endpointCallWithCapsOnCore_no_caps _ _ _ _ _ _ _ (by rw [hCaps]; rfl), hStamp, hEq]
  simp only [Except.map, hEp, hH, hcv, hrv]
  unfold applyCallDonationOnCore
  rw [applyCallDonation_eq_ok_self_of_no_donation _ _ _ (by rw [hcv', hrv']; exact hDon)]
  simp only [hcv', hrv', hDon]
  rfl

end SeLe4n.Kernel
