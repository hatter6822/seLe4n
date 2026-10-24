/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.DualQueue.PopInPlace
import SeLe4n.Kernel.IPC.DualQueue.Transport

/-!
# A waiter removed from anywhere in an endpoint queue, in place

WS-ZA ZA5.4 part 24: the removal of an arbitrary waiter from an endpoint queue
(`endpointQueueRemoveDual`, the removal the rendezvous paths use), written as one
rewrite of each object it touches where that object stands (`storeQueueRemove`),
and proven equal to the specification's removal whenever every store stays in
its slot (`queueRemoveInPlace`, `queueRemove_inPlace`).  The final delete of a
thread blocked sending, calling or receiving takes the thread off its queue this
way, wherever in the queue it waits, as seL4's `cancelIPC` does through
`tcbEPDequeue`.  It is the head pop's generalisation (`storePopHead`,
`popHead_inPlace`) and stated beside it so that any other cancel of a queued
thread can take the same form.

Every write is a scalar code written in its cell: the endpoint's queue ends
(`headAdvancedEndpoint`, `endsSetEndpoint`), the neighbours' link codes
(`queueUnlinkPredecessor`, `queueUnlinkSuccessor`) and the removed thread's
(`tcbOffQueue`).  The writes are the specification's own, in its order, so
the proof is the specification's steps read one at a time.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood

/-- **The end code a removal leaves at one queue boundary**: `endCode`, unless it
named the removed thread (whose code is `tidCode`), and then `replacement`
(`queueRemoveBoundary`, on codes). -/
@[inline] def removedEndCode (endCode tidCode replacement : Nat) : Nat :=
  if endCode == tidCode then replacement else endCode

/-- The endpoint whose receive queue (`isReceiveQ`) or send queue starts at the
thread `nextCode` names, its tail kept: the write the removal of a queue's head
makes first. -/
@[inline] def headAdvancedEndpoint (isReceiveQ : Bool) (nextCode : Nat) :
    KernelObject → KernelObject
  | .endpoint e => .endpoint
      (if isReceiveQ then { e with recvHeadCode := nextCode } else { e with sendHeadCode := nextCode })
  | o => o

/-- The endpoint with both ends of its receive queue (`isReceiveQ`) or its send
queue written as codes. -/
@[inline] def endsSetEndpoint (isReceiveQ : Bool) (headCode tailCode : Nat) :
    KernelObject → KernelObject
  | .endpoint e => .endpoint
      (if isReceiveQ then { e with recvHeadCode := headCode, recvTailCode := tailCode }
       else { e with sendHeadCode := headCode, sendTailCode := tailCode })
  | o => o

/-- The head code of one of `ep`'s queues. -/
@[inline] def _root_.SeLe4n.Model.Endpoint.headCodeOf (ep : Endpoint) (isReceiveQ : Bool) : Nat :=
  if isReceiveQ then ep.recvHeadCode else ep.sendHeadCode

/-- The tail code of one of `ep`'s queues. -/
@[inline] def _root_.SeLe4n.Model.Endpoint.tailCodeOf (ep : Endpoint) (isReceiveQ : Bool) : Nat :=
  if isReceiveQ then ep.recvTailCode else ep.sendTailCode

/-- **The removal of `tid` (whose TCB is `tcb`) from one of the queues of the
endpoint `ep` at `endpointId`, each write in its slot**, in the specification's
order: a removed head advances the queue's head; otherwise the predecessor skips
it; the successor inherits its back links; the queue's two ends are written;
and the thread is unlinked. -/
@[inline] def storeQueueRemove (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) : SystemState :=
  let headCode := removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode
  let tailCode := removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode
  let s1 := match tcb.queuePPrev with
    | some .endpointHead => st.modifyObject endpointId (headAdvancedEndpoint isReceiveQ tcb.queueNextCode)
    | some (.tcbNext p) => st.updateTcb p (queueUnlinkPredecessor tcb)
    | none => st
  let s2 := match tcb.queueNext with
    | some n => s1.updateTcb n (queueUnlinkSuccessor tcb)
    | none => s1
  (s2.modifyObject endpointId (endsSetEndpoint isReceiveQ headCode tailCode)).updateTcb tid
    tcbOffQueue

/-- **Whether the removal of `tid` writes only its slots**: the specification's
own checks pass (`dualQueueRemovalEnabled`, and a predecessor names the thread,
`queuePredecessorNamesSuccessor`), and the endpoint, the thread, its predecessor
and its successor are each rewritten where they stand (`RHTable.findsInPlace`),
each store changing only `objects` (`storeLeavesIndexAndTypes`), the three
threads distinct unreserved TCBs. -/
@[inline] def queueRemoveInPlace (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) : Bool :=
  !tid.isReserved &&
  storeLeavesIndexAndTypes st endpointId .endpoint && st.objects.findsInPlace endpointId &&
  storeLeavesIndexAndTypes st tid.toObjId .tcb && st.objects.findsInPlace tid.toObjId &&
  (match tcb.queuePPrev with
   | none => false
   | some pprev =>
     dualQueueRemovalEnabled (if isReceiveQ then ep.receiveQ else ep.sendQ) tid tcb pprev &&
     match pprev with
     | .endpointHead => true
     | .tcbNext p => !p.isReserved && p != tid &&
         storeLeavesIndexAndTypes st p.toObjId .tcb && st.objects.findsInPlace p.toObjId &&
         match st.getTcb? p with
         | some pt => queuePredecessorNamesSuccessor pt tid
         | none => false) &&
  (match tcb.queueNext with
   | none => true
   | some n => !n.isReserved && n != tid && tcb.queuePrev != some n &&
       storeLeavesIndexAndTypes st n.toObjId .tcb && st.objects.findsInPlace n.toObjId &&
       (st.getTcb? n).isSome)

/-- **Whether `t` is blocked on the side of the endpoint `endpointId` a removal
from its receive queue (`isReceiveQ`) or its send queue acts on**, read from its
two IPC codes (`ThreadIpcState.ofCodes`): receiving there, or sending or calling
there. -/
@[inline] def blockedOnQueueSide (isReceiveQ : Bool) (endpointId : SeLe4n.ObjId) (t : TCB) :
    Bool :=
  if isReceiveQ then t.ipcStateCode == 1 && t.ipcObjectCode == endpointId.val
  else (t.ipcStateCode == 0 && t.ipcObjectCode == endpointId.val + 1) ||
    (t.ipcStateCode == 3 && t.ipcObjectCode == endpointId.val)

/-- What `blockedOnQueueSide` reads: the thread's IPC state. -/
theorem blockedOnQueueSide_ipcState {isReceiveQ : Bool} {endpointId : SeLe4n.ObjId} {t : TCB}
    (h : blockedOnQueueSide isReceiveQ endpointId t = true) :
    (isReceiveQ = true → t.ipcState = .blockedOnReceive endpointId) ∧
      (isReceiveQ = false →
        t.ipcState = .blockedOnSend endpointId ∨ t.ipcState = .blockedOnCall endpointId) := by
  unfold blockedOnQueueSide at h
  cases isReceiveQ
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at h
    refine ⟨fun h' => absurd h' (by decide), fun _ => ?_⟩
    rcases h with ⟨hS, hO⟩ | ⟨hS, hO⟩
    · left; simp only [TCB.ipcState, hS, hO, ThreadIpcState.ofCodes]
    · right; simp only [TCB.ipcState, hS, hO, ThreadIpcState.ofCodes]
  · simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨fun _ => ?_, fun h' => absurd h' (by decide)⟩
    simp only [TCB.ipcState, h.1, h.2, ThreadIpcState.ofCodes]

-- ============================================================================
-- The writes, as the specification's values
-- ============================================================================

/-- A removal's end code is the code of the boundary `queueRemoveBoundary`
leaves. -/
theorem optCode_removedBoundary (c : Nat) (tid : SeLe4n.ThreadId) (r : Option SeLe4n.ThreadId) :
    SeLe4n.ThreadId.optCode
      (if SeLe4n.ThreadId.ofOptCode c = some tid then r else SeLe4n.ThreadId.ofOptCode c) =
      removedEndCode c (tid.val + 1) (SeLe4n.ThreadId.optCode r) := by
  unfold removedEndCode
  by_cases h : c = tid.val + 1
  · subst h; simp [SeLe4n.ThreadId.ofOptCode]
  · have hNe : SeLe4n.ThreadId.ofOptCode c ≠ some tid := by
      intro e; apply h; rw [← SeLe4n.ThreadId.optCode_ofOptCode c, e]; rfl
    simp only [hNe, ↓reduceIte, SeLe4n.ThreadId.optCode_ofOptCode, beq_iff_eq, h]

/-- **The ends written are the specification's boundary**: on the endpoint the
removal started from, `endsSetEndpoint` writes the queue `queueRemoveBoundary`
computes. -/
theorem endsSetEndpoint_removed (isReceiveQ : Bool) (ep : Endpoint) (tid : SeLe4n.ThreadId)
    (tcb : TCB) :
    endsSetEndpoint isReceiveQ
        (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
        (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode)
        (.endpoint ep) =
      .endpoint (if isReceiveQ then
          ep.withReceiveQ (queueRemoveBoundary (if isReceiveQ then ep.receiveQ else ep.sendQ) tid tcb)
        else ep.withSendQ (queueRemoveBoundary (if isReceiveQ then ep.receiveQ else ep.sendQ) tid tcb)) := by
  cases isReceiveQ <;>
  simp only [endsSetEndpoint, Endpoint.withReceiveQ, Endpoint.withSendQ, queueRemoveBoundary,
    Endpoint.receiveQ, Endpoint.sendQ, optCode_removedBoundary, TCB.optCode_queueNext,
    TCB.optCode_queuePrev, Endpoint.headCodeOf, Endpoint.tailCodeOf, Bool.false_eq_true,
    ↓reduceIte]

/-- Writing both ends overwrites an advanced head. -/
theorem endsSetEndpoint_headAdvanced (isReceiveQ : Bool) (h t c : Nat) (o : KernelObject) :
    endsSetEndpoint isReceiveQ h t (headAdvancedEndpoint isReceiveQ c o) =
      endsSetEndpoint isReceiveQ h t o := by
  cases o <;> cases isReceiveQ <;> rfl

/-- **The head's advance is the specification's first write**: the queue starts
at the removed head's successor and keeps its tail. -/
theorem headAdvancedEndpoint_eq (isReceiveQ : Bool) (ep : Endpoint) (tcb : TCB) :
    headAdvancedEndpoint isReceiveQ tcb.queueNextCode (.endpoint ep) =
      .endpoint (if isReceiveQ then
          ep.withReceiveQ ⟨tcb.queueNext, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩
        else ep.withSendQ ⟨tcb.queueNext, (if isReceiveQ then ep.receiveQ else ep.sendQ).tail⟩) := by
  cases isReceiveQ <;>
  simp only [headAdvancedEndpoint, Endpoint.withReceiveQ_head, Endpoint.withSendQ_head,
    TCB.optCode_queueNext, Bool.false_eq_true, ↓reduceIte]

/-- **The predecessor's skip is the specification's link store**: the
predecessor's links rewritten with the removed thread's successor. -/
theorem tcbWithQueueLinks_predecessor (removed p : TCB) :
    tcbWithQueueLinks p p.queuePrev p.queuePPrev removed.queueNext =
      queueUnlinkPredecessor removed p := by
  simp only [tcbWithQueueLinks, TCB.optCode_queuePrev, TCB.optCode_queuePPrev,
    TCB.optCode_queueNext, queueUnlinkPredecessor]

/-- **The successor's back links are the specification's link store**. -/
theorem tcbWithQueueLinks_successor (removed n : TCB) {pprev : QueuePPrev}
    (hP : removed.queuePPrev = some pprev) :
    tcbWithQueueLinks n removed.queuePrev (some pprev) n.queueNext =
      queueUnlinkSuccessor removed n := by
  rw [← hP]
  simp only [tcbWithQueueLinks, TCB.optCode_queuePrev, TCB.optCode_queuePPrev,
    TCB.optCode_queueNext, queueUnlinkSuccessor]

-- ============================================================================
-- Writes in their slots
-- ============================================================================

/-- **An object rewritten in its slot**: `modifyObject` of a present key is the
insert of its new value, and an insert in place keeps every key's in-place
question, every other key's object and every local store local. -/
theorem modifyObject_inPlace {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (f : KernelObject → KernelObject) (hO : st.objects[k]? = some o)
    (hF : st.objects.findsInPlace k = true) (hNotV : ∀ r, f o ≠ .vspaceRoot r) :
    st.modifyObject k f = { st with objects := st.objects.insert k (f o) } ∧
    (∀ k', (st.modifyObject k f).objects.findsInPlace k' = st.objects.findsInPlace k') ∧
    (∀ k', k ≠ k' → (st.modifyObject k f).objects[k']? = st.objects[k']?) ∧
    (st.modifyObject k f).objects[k]? = some (f o) ∧
    (∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
      storeLeavesIndexAndTypes (st.modifyObject k f) id ty = true) := by
  have hEq : st.modifyObject k f = { st with objects := st.objects.insert k (f o) } := by
    unfold SystemState.modifyObject; rw [RHTable.modify_of_get? hO]
  refine ⟨hEq, fun k' => ?_, fun k' hk => ?_, ?_, fun h => ?_⟩
  · rw [hEq]; exact RHTable.findsInPlace_insert_of_findsInPlace k' _ hF
  · rw [hEq]; exact RHTable.get?_insert_ne_of_findsInPlace k' _ hF hk
  · rw [hEq]; exact RHTable.get?_insert_self_of_findsInPlace _ hF
  · rw [hEq]; exact storeLeavesIndexAndTypes_insert_inPlace hF hNotV h

/-- A store of an endpoint that changes only `objects` is the modify of its slot
by any update giving that endpoint. -/
theorem storeObject_endpoint_eq_modifyObject {st : SystemState} {k : SeLe4n.ObjId}
    {o : KernelObject} {ep' : Endpoint} (f : KernelObject → KernelObject)
    (hO : st.objects[k]? = some o) (hf : f o = .endpoint ep')
    (hL : storeLeavesIndexAndTypes st k .endpoint = true) :
    storeObject k (.endpoint ep') st = .ok ((), st.modifyObject k f) := by
  rw [storeObject_eq_of_leaves (by simpa only [KernelObject.objectType] using hL)]
  unfold SystemState.modifyObject; rw [RHTable.modify_of_get? hO, hf]

/-- A link store of a present, unreserved thread that changes only `objects` is
the rewrite of its slot by any update giving those links. -/
theorem storeTcbQueueLinks_eq_updateTcb {st : SystemState} {t : SeLe4n.ThreadId} {tt : TCB}
    (g : TCB → TCB) (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) (hR : t.isReserved = false) (hT : st.getTcb? t = some tt)
    (hL : storeLeavesIndexAndTypes st t.toObjId .tcb = true)
    (hg : tcbWithQueueLinks tt prev pprev next = g tt) :
    storeTcbQueueLinks st t prev pprev next = .ok (st.updateTcb t g) := by
  unfold storeTcbQueueLinks
  rw [modifyTcb_eq_updateTcb _ hR hT hL, SystemState.updateTcb_eq_of_some hT,
    SystemState.updateTcb_eq_of_some hT, hg]

-- ============================================================================
-- The removal, in place
-- ============================================================================

/-- **What a removal written in place leaves**: the removed thread unlinked,
every key found where it was, every store still local, and every key other than
the endpoint, the thread and its two neighbours untouched. -/
structure QueueRemoveFrame (st s : SystemState) (endpointId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) : Prop where
  removed_tcb : s.getTcb? tid = some (tcbOffQueue tcb)
  keepsFinds : s.objectsKeepFinds st
  leaves : ∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
    storeLeavesIndexAndTypes s id ty = true
  other : ∀ x, endpointId ≠ x → tid.toObjId ≠ x → (∀ p, tcb.queuePrev = some p → p.toObjId ≠ x) →
    (∀ n, tcb.queueNext = some n → n.toObjId ≠ x) → s.objects[x]? = st.objects[x]?

/-- **The removal's last two writes, in place**: the queue's ends written over
whatever the first steps left at the endpoint, then the thread unlinked. -/
theorem queueRemove_finish {S2 : SystemState} {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {ep : Endpoint} {cur : KernelObject} {tcb : TCB}
    (hE2 : S2.objects[endpointId]? = some cur)
    (hCur : ∀ h t, endsSetEndpoint isReceiveQ h t cur =
      endsSetEndpoint isReceiveQ h t (.endpoint ep))
    (hFE : S2.objects.findsInPlace endpointId = true)
    (hLE : storeLeavesIndexAndTypes S2 endpointId .endpoint = true)
    (hR : tid.isReserved = false)
    (hT2 : S2.objects[tid.toObjId]? = some (.tcb tcb))
    (hFT : S2.objects.findsInPlace tid.toObjId = true)
    (hLT : storeLeavesIndexAndTypes S2 tid.toObjId .tcb = true)
    (hNe : endpointId ≠ tid.toObjId) :
    let S3 := S2.modifyObject endpointId (endsSetEndpoint isReceiveQ
      (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
      (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))
    storeObject endpointId (.endpoint (if isReceiveQ then
          ep.withReceiveQ (queueRemoveBoundary (if isReceiveQ then ep.receiveQ else ep.sendQ) tid tcb)
        else ep.withSendQ (queueRemoveBoundary (if isReceiveQ then ep.receiveQ else ep.sendQ) tid tcb)))
        S2 = .ok ((), S3) ∧
      storeTcbQueueLinks S3 tid none none none = .ok (S3.updateTcb tid tcbOffQueue) ∧
      (S3.updateTcb tid tcbOffQueue).getTcb? tid = some (tcbOffQueue tcb) ∧
      (S3.updateTcb tid tcbOffQueue).objectsKeepFinds S2 ∧
      (∀ {id ty}, storeLeavesIndexAndTypes S2 id ty = true →
        storeLeavesIndexAndTypes (S3.updateTcb tid tcbOffQueue) id ty = true) ∧
      (∀ x, endpointId ≠ x → tid.toObjId ≠ x →
        (S3.updateTcb tid tcbOffQueue).objects[x]? = S2.objects[x]?) := by
  intro S3
  have hf := (hCur (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
    (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode)).trans
    (endsSetEndpoint_removed isReceiveQ ep tid tcb)
  obtain ⟨-, hF3, hG3, -, hL3⟩ := modifyObject_inPlace (endsSetEndpoint isReceiveQ
      (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
      (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))
    hE2 hFE (by rw [hf]; intro r h; cases h)
  have hT3 : S3.getTcb? tid = some tcb :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr ((hG3 _ hNe).trans hT2)
  have hFT3 : S3.objects.findsInPlace tid.toObjId = true := (hF3 _).trans hFT
  exact ⟨storeObject_endpoint_eq_modifyObject _ hE2 hf hLE,
    storeTcbQueueLinks_eq_updateTcb tcbOffQueue none none none hR hT3 (hL3 hLT) rfl,
    updateTcb_getTcb?_self_of_findsInPlace _ hT3 hFT3,
    fun k => (updateTcb_findsInPlace _ hT3 hFT3 k).trans (hF3 k),
    fun h => updateTcb_storeLeaves _ hT3 hFT3 (hL3 h),
    fun x hEx hTx => (updateTcb_get?_ne_of_findsInPlace _ hT3 hFT3 hTx).trans (hG3 x hEx)⟩

/-- **The removal of a waiter from an endpoint queue, in place**: under
`queueRemoveInPlace` the specification's removal (`endpointQueueRemoveDual`)
succeeds with `storeQueueRemove`'s state, which keeps the removal's frame. -/
theorem queueRemove_inPlace (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep))
    (hT : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hG : queueRemoveInPlace st endpointId isReceiveQ tid ep tcb = true) :
    endpointQueueRemoveDual endpointId isReceiveQ tid st =
        .ok ((), storeQueueRemove st endpointId isReceiveQ tid ep tcb) ∧
      QueueRemoveFrame st (storeQueueRemove st endpointId isReceiveQ tid ep tcb) endpointId tid
        tcb := by
  unfold queueRemoveInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨⟨⟨⟨⟨hR, hLE⟩, hFE⟩, hLT⟩, hFT⟩, hPrevG⟩, hNextG⟩ := hG
  have hNeET : endpointId ≠ tid.toObjId := by intro h; rw [h, hT] at hE; cases hE
  have hTg : st.getTcb? tid = some tcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hLook : lookupTcb st tid = some tcb := by
    simp only [lookupTcb, hR, Bool.false_eq_true, ↓reduceIte]; exact hTg
  cases hPP : tcb.queuePPrev with
  | none => rw [hPP] at hPrevG; cases hPrevG
  | some pprev =>
  rw [hPP] at hPrevG
  simp only [Bool.and_eq_true] at hPrevG
  obtain ⟨hEn, hPrevG⟩ := hPrevG
  unfold endpointQueueRemoveDual storeQueueRemove
  simp only [SystemState.getObject?, hE, hLook, hPP, hEn, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  -- The successor's step and the last two writes, on whatever the first step left.
  have rest : ∀ (S1 : SystemState) (cur : KernelObject),
      S1.objects[endpointId]? = some cur →
      (∀ h t, endsSetEndpoint isReceiveQ h t cur = endsSetEndpoint isReceiveQ h t (.endpoint ep)) →
      (∀ k, S1.objects.findsInPlace k = st.objects.findsInPlace k) →
      (∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
        storeLeavesIndexAndTypes S1 id ty = true) →
      S1.objects[tid.toObjId]? = some (.tcb tcb) →
      (∀ n, tcb.queueNext = some n → n.toObjId ≠ endpointId →
        S1.objects[n.toObjId]? = st.objects[n.toObjId]?) →
      (match (match tcb.queueNext with
        | none => Except.ok S1
        | some nextTid =>
          match lookupTcb S1 nextTid with
          | none => Except.error KernelError.objectNotFound
          | some nextTcb =>
            storeTcbQueueLinks S1 nextTid tcb.queuePrev (some pprev) nextTcb.queueNext) with
      | Except.error e => Except.error e
      | Except.ok st2 =>
        match storeObject endpointId (KernelObject.endpoint (if isReceiveQ = true then
            ep.withReceiveQ (queueRemoveBoundary (if isReceiveQ = true then ep.receiveQ else ep.sendQ) tid tcb)
          else ep.withSendQ (queueRemoveBoundary (if isReceiveQ = true then ep.receiveQ else ep.sendQ) tid tcb)))
          st2 with
        | Except.error e => Except.error e
        | Except.ok (PUnit.unit, st3) =>
          match storeTcbQueueLinks st3 tid none none none with
          | Except.error e => Except.error e
          | Except.ok st4 => Except.ok ((), st4)) =
        Except.ok ((), ((match tcb.queueNext with
            | some n => S1.updateTcb n (queueUnlinkSuccessor tcb)
            | none => S1).modifyObject endpointId (endsSetEndpoint isReceiveQ
              (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
              (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))).updateTcb
            tid tcbOffQueue) ∧
      (((match tcb.queueNext with
            | some n => S1.updateTcb n (queueUnlinkSuccessor tcb)
            | none => S1).modifyObject endpointId (endsSetEndpoint isReceiveQ
              (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
              (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))).updateTcb
            tid tcbOffQueue).getTcb? tid = some (tcbOffQueue tcb) ∧
      (∀ k, (((match tcb.queueNext with
            | some n => S1.updateTcb n (queueUnlinkSuccessor tcb)
            | none => S1).modifyObject endpointId (endsSetEndpoint isReceiveQ
              (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
              (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))).updateTcb
            tid tcbOffQueue).objects.findsInPlace k = st.objects.findsInPlace k) ∧
      (∀ {id ty}, storeLeavesIndexAndTypes st id ty = true →
        storeLeavesIndexAndTypes (((match tcb.queueNext with
            | some n => S1.updateTcb n (queueUnlinkSuccessor tcb)
            | none => S1).modifyObject endpointId (endsSetEndpoint isReceiveQ
              (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
              (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))).updateTcb
            tid tcbOffQueue) id ty = true) ∧
      (∀ x, endpointId ≠ x → tid.toObjId ≠ x → (∀ n, tcb.queueNext = some n → n.toObjId ≠ x) →
        (((match tcb.queueNext with
            | some n => S1.updateTcb n (queueUnlinkSuccessor tcb)
            | none => S1).modifyObject endpointId (endsSetEndpoint isReceiveQ
              (removedEndCode (ep.headCodeOf isReceiveQ) (tid.val + 1) tcb.queueNextCode)
              (removedEndCode (ep.tailCodeOf isReceiveQ) (tid.val + 1) tcb.queuePrevCode))).updateTcb
            tid tcbOffQueue).objects[x]? = S1.objects[x]?) := by
    intro S1 cur hE1 hCur hF1 hL1 hT1 hN1
    cases hN : tcb.queueNext with
    | none =>
      obtain ⟨h3, h4, hTT, hKF, hLL, hOO⟩ := queueRemove_finish (S2 := S1) hE1 hCur
        ((hF1 _).trans hFE) (hL1 hLE) hR hT1 ((hF1 _).trans hFT) (hL1 hLT) hNeET
      simp only []
      rw [h3]; simp only []; rw [h4]
      exact ⟨rfl, hTT, fun k => (hKF k).trans (hF1 k), fun h => hLL (hL1 h),
        fun x hEx hTx _ => hOO x hEx hTx⟩
    | some n =>
      rw [hN] at hNextG
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hNextG
      obtain ⟨⟨⟨⟨⟨hRn, hNeN⟩, -⟩, hLn⟩, hFn⟩, hTnB⟩ := hNextG
      obtain ⟨nt, hTn⟩ := Option.isSome_iff_exists.mp hTnB
      have hTno := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTn
      have hNeEN : n.toObjId ≠ endpointId := by intro h; rw [h, hE] at hTno; cases hTno
      have hTn1 : S1.getTcb? n = some nt :=
        (SystemState.getTcb?_eq_some_iff _ _ _).mpr ((hN1 n hN hNeEN).trans hTno)
      have hLookN : lookupTcb S1 n = some nt := by
        simp only [lookupTcb, hRn, Bool.false_eq_true, ↓reduceIte]; exact hTn1
      have hFn1 : S1.objects.findsInPlace n.toObjId = true := (hF1 _).trans hFn
      have hS2 := storeTcbQueueLinks_eq_updateTcb (queueUnlinkSuccessor tcb) _ _ _ hRn hTn1
        (hL1 hLn) (tcbWithQueueLinks_successor tcb nt hPP)
      have hNeNT : n.toObjId ≠ tid.toObjId := fun h => hNeN (SeLe4n.ThreadId.toObjId_injective _ _ h)
      generalize hS2d : S1.updateTcb n (queueUnlinkSuccessor tcb) = S2 at hS2
      have hF2 : ∀ k, S2.objects.findsInPlace k = S1.objects.findsInPlace k := fun k => by
        rw [← hS2d]; exact updateTcb_findsInPlace _ hTn1 hFn1 k
      have hG2 : ∀ k, n.toObjId ≠ k → S2.objects[k]? = S1.objects[k]? := fun k hk => by
        rw [← hS2d]; exact updateTcb_get?_ne_of_findsInPlace _ hTn1 hFn1 hk
      have hL2 : ∀ {id ty}, storeLeavesIndexAndTypes S1 id ty = true →
          storeLeavesIndexAndTypes S2 id ty = true := fun h => by
        rw [← hS2d]; exact updateTcb_storeLeaves _ hTn1 hFn1 h
      obtain ⟨h3, h4, hTT, hKF, hLL, hOO⟩ := queueRemove_finish (S2 := S2)
        ((hG2 _ hNeEN).trans hE1) hCur ((hF2 _).trans ((hF1 _).trans hFE))
        (hL2 (hL1 hLE)) hR ((hG2 _ hNeNT).trans hT1) ((hF2 _).trans ((hF1 _).trans hFT))
        (hL2 (hL1 hLT)) hNeET
      simp only [hLookN, hS2]
      rw [h3]; simp only []; rw [h4]
      subst hS2d
      exact ⟨rfl, hTT, fun k => (hKF k).trans ((hF2 k).trans (hF1 k)),
        fun h => hLL (hL2 (hL1 h)),
        fun x hEx hTx hNx => (hOO x hEx hTx).trans (hG2 x (hNx n rfl))⟩
  cases pprev with
  | endpointHead =>
    obtain ⟨-, hF1, hG1, hE1, hL1⟩ := modifyObject_inPlace
      (headAdvancedEndpoint isReceiveQ tcb.queueNextCode) hE hFE
      (by rw [headAdvancedEndpoint_eq]; intro r h; cases h)
    have hS1 := storeObject_endpoint_eq_modifyObject
      (headAdvancedEndpoint isReceiveQ tcb.queueNextCode) hE
      (headAdvancedEndpoint_eq isReceiveQ ep tcb) hLE
    simp only [hS1]
    obtain ⟨hR1, hT', hF', hL', hO'⟩ := rest _ _ hE1
      (fun h t => endsSetEndpoint_headAdvanced isReceiveQ h t _ _) hF1 hL1
      ((hG1 _ hNeET).trans hT) (fun n _ hNe => hG1 _ (Ne.symm hNe))
    exact ⟨hR1, { removed_tcb := hT', keepsFinds := hF', leaves := hL'
                  other := fun x hEx hTx _ hNx => (hO' x hEx hTx hNx).trans (hG1 x hEx) }⟩
  | tcbNext p =>
    have hQP : tcb.queuePrev = some p := by
      have hGd := dualQueueRemovalEnabled_guard hEn
      unfold dualQueueRemovalGuard at hGd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hGd
      exact hGd.2.2
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hPrevG
    obtain ⟨⟨⟨⟨hRp, hNePT⟩, hLp⟩, hFp⟩, hNames⟩ := hPrevG
    cases hTp : st.getTcb? p with
    | none => rw [hTp] at hNames; cases hNames
    | some pt =>
    rw [hTp] at hNames
    have hLookP : lookupTcb st p = some pt := by
      simp only [lookupTcb, hRp, Bool.false_eq_true, ↓reduceIte]; exact hTp
    have hS1 := storeTcbQueueLinks_eq_updateTcb (queueUnlinkPredecessor tcb) _ _ _ hRp hTp hLp
      (tcbWithQueueLinks_predecessor tcb pt)
    simp only [hLookP, hNames, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hS1]
    have hTpo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTp
    have hNePE : p.toObjId ≠ endpointId := by intro h; rw [h, hE] at hTpo; cases hTpo
    have hNePT' : p.toObjId ≠ tid.toObjId := fun h =>
      hNePT (SeLe4n.ThreadId.toObjId_injective _ _ h)
    have hF1 : ∀ k, (st.updateTcb p (queueUnlinkPredecessor tcb)).objects.findsInPlace k =
        st.objects.findsInPlace k := updateTcb_findsInPlace _ hTp hFp
    have hG1 : ∀ k, p.toObjId ≠ k →
        (st.updateTcb p (queueUnlinkPredecessor tcb)).objects[k]? = st.objects[k]? :=
      fun k hk => updateTcb_get?_ne_of_findsInPlace _ hTp hFp hk
    obtain ⟨hR1, hT', hF', hL', hO'⟩ := rest _ _ ((hG1 _ hNePE).trans hE)
      (fun _ _ => rfl) hF1 (fun h => updateTcb_storeLeaves _ hTp hFp h)
      ((hG1 _ hNePT').trans hT) (fun n hN _ => hG1 _ (by
        intro h
        have := SeLe4n.ThreadId.toObjId_injective _ _ h
        subst this
        revert hNextG
        simp [hN, hQP]))
    exact ⟨hR1, { removed_tcb := hT', keepsFinds := hF', leaves := hL'
                  other := fun x hEx hTx hPx hNx =>
                    (hO' x hEx hTx hNx).trans (hG1 x (hPx p hQP)) }⟩

end SeLe4n.Kernel
