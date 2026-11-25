-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.NotificationLinks

/-! # The endpoint queues' link writes

WS-SX SX24 (D46, D47).  The writers of an endpoint's queue ends and of a
thread's endpoint-queue links keep `endpointQueueLabelsAgree`: each new end or
link names a thread whose label the agreement already gives — the popped head's
successor carries the head's label and the head the endpoint's, a removed
thread's neighbours carry its label, and the appended thread carries the
endpoint's by the gate its entry checks (`EndpointQueueLabelsGrowAt`).  Each
proof reads labels only, never the queue's shape.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

namespace endpointQueueLabelsAgree

variable {ctx : LabelingContext}

/-- **One slot rewritten**, the others kept. -/
theorem of_slot {st st' : SystemState} {k : SeLe4n.ObjId} (H : endpointQueueLabelsAgree ctx st)
    (hNe : ∀ j, j ≠ k → st'.objects[j]? = st.objects[j]?)
    (hSelf : ∀ o', st'.objects[k]? = some o' → endpointQueueEntryLabelsAgree ctx k o') :
    endpointQueueLabelsAgree ctx st' := fun oid obj' hO => by
  by_cases hk : oid = k
  · subst hk; exact hSelf obj' hO
  · rw [hNe _ hk] at hO; exact H oid obj' hO

/-- A raw insert. -/
theorem insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject} (hInv : st.objects.invExt)
    (H : endpointQueueLabelsAgree ctx st) (hSelf : endpointQueueEntryLabelsAgree ctx k o) :
    endpointQueueLabelsAgree ctx { st with objects := st.objects.insert k o } :=
  of_slot H (fun j hj => by
      show (st.objects.insert k o)[j]? = _
      simp only [RHTable_getElem?_eq_get?]
      exact RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hj (eq_of_beq hb).symm) hInv)
    fun o' hO => by
      have : (st.objects.insert k o)[k]? = some o := by
        simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
      rw [show ({ st with objects := st.objects.insert k o } : SystemState).objects[k]? = _ from this] at hO
      cases hO; exact hSelf

/-- A store. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (H : endpointQueueLabelsAgree ctx st) (hSelf : endpointQueueEntryLabelsAgree ctx k o) :
    endpointQueueLabelsAgree ctx st' :=
  of_slot H (fun j hj => storeObject_objects_ne st st' k j o hj hInv h) fun o' hO => by
    rw [storeObject_objects_eq st st' k o hInv h] at hO
    cases hO; exact hSelf

/-- **The unchecked TCB write.** -/
theorem updateTcb {st : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (H : endpointQueueLabelsAgree ctx st)
    (hSelf : ∀ x, st.objects[t.toObjId]? = some (.tcb x) →
      endpointQueueEntryLabelsAgree ctx t.toObjId (.tcb (f x))) :
    endpointQueueLabelsAgree ctx (st.updateTcb t f) := by
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact H
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT]
    exact insert hInv H (hSelf x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT))

/-- **The checked TCB write.** -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st')
    (H : endpointQueueLabelsAgree ctx st)
    (hSelf : ∀ x, st.objects[t.toObjId]? = some (.tcb x) →
      endpointQueueEntryLabelsAgree ctx t.toObjId (.tcb (f x))) :
    endpointQueueLabelsAgree ctx st' := by
  obtain ⟨tcb, hL, hSt⟩ := modifyTcb_ok_decompose h
  exact storeObject hInv hSt H (hSelf tcb (lookupTcb_some_objects st t tcb hL))

/-- What the agreement says of a stored thread's links. -/
theorem links {st : SystemState} (H : endpointQueueLabelsAgree ctx st) {t : SeLe4n.ThreadId}
    {x : TCB} (hO : st.objects[t.toObjId]? = some (.tcb x)) :
    (∀ u, x.queuePrev = some u → ctx.threadLabelOf u = ctx.threadLabelOf t) ∧
      (∀ u, x.queueNext = some u → ctx.threadLabelOf u = ctx.threadLabelOf t) :=
  H _ _ hO

/-- What the agreement says of a stored endpoint's queues. -/
theorem ends {st : SystemState} (H : endpointQueueLabelsAgree ctx st) {e : SeLe4n.ObjId}
    {ep : Endpoint} (hO : st.objects[e]? = some (.endpoint ep)) :
    queueEndsLabelled ctx (ctx.endpointLabelOf e) ep.sendQ ∧
      queueEndsLabelled ctx (ctx.endpointLabelOf e) ep.receiveQ :=
  H _ _ hO

/-- One of the endpoint's queues, by `isReceiveQ`. -/
theorem endsOf {st : SystemState} (H : endpointQueueLabelsAgree ctx st) {e : SeLe4n.ObjId}
    {ep : Endpoint} (hO : st.objects[e]? = some (.endpoint ep)) (isReceiveQ : Bool) :
    queueEndsLabelled ctx (ctx.endpointLabelOf e) (if isReceiveQ then ep.receiveQ else ep.sendQ) := by
  cases isReceiveQ
  · exact (ends H hO).1
  · exact (ends H hO).2

/-- **A thread's share, its links stated.** -/
theorem tcb_entry {t : SeLe4n.ThreadId} {y : TCB}
    (hP : ∀ u, y.queuePrev = some u → ctx.threadLabelOf u = ctx.threadLabelOf t)
    (hN : ∀ u, y.queueNext = some u → ctx.threadLabelOf u = ctx.threadLabelOf t) :
    endpointQueueEntryLabelsAgree ctx t.toObjId (.tcb y) := ⟨hP, hN⟩

/-- **An endpoint with one queue replaced**, the new queue's ends labelled. -/
theorem endpoint_entry_withQ {e : SeLe4n.ObjId} {ep : Endpoint} (isReceiveQ : Bool)
    {q : IntrusiveQueue} (hOld : endpointQueueEntryLabelsAgree ctx e (.endpoint ep))
    (hq : queueEndsLabelled ctx (ctx.endpointLabelOf e) q) :
    endpointQueueEntryLabelsAgree ctx e
      (.endpoint (if isReceiveQ then ep.withReceiveQ q else ep.withSendQ q)) := by
  cases isReceiveQ
  · simp only [Bool.false_eq_true, if_false]
    exact ⟨by simpa using hq, by simpa using hOld.2⟩
  · simp only [if_true]
    exact ⟨by simpa using hOld.1, by simpa using hq⟩

/-- **A thread's three endpoint-queue links written**, each new neighbour of its
label. -/
theorem storeTcbQueueLinks {st st' : SystemState} {t : SeLe4n.ThreadId}
    {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev} {next : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbQueueLinks st t prev pprev next = .ok st')
    (H : endpointQueueLabelsAgree ctx st)
    (hP : ∀ u, prev = some u → ctx.threadLabelOf u = ctx.threadLabelOf t)
    (hN : ∀ u, next = some u → ctx.threadLabelOf u = ctx.threadLabelOf t) :
    endpointQueueLabelsAgree ctx st' :=
  modifyTcb hInv h H fun _ _ => tcb_entry (by simpa using hP) (by simpa using hN)

/-- **A removal's boundaries**: an end that named the removed thread moves to
its neighbour, which carries its label. -/
theorem queueRemoveBoundary_labelled {l : SecurityLabel} {q : IntrusiveQueue}
    {tid : SeLe4n.ThreadId} {removed : TCB} (hq : queueEndsLabelled ctx l q)
    (hP : ∀ u, removed.queuePrev = some u → ctx.threadLabelOf u = ctx.threadLabelOf tid)
    (hN : ∀ u, removed.queueNext = some u → ctx.threadLabelOf u = ctx.threadLabelOf tid) :
    queueEndsLabelled ctx l (queueRemoveBoundary q tid removed) := by
  unfold queueRemoveBoundary
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · dsimp only at ht
    split at ht
    · rename_i h; rw [hN t ht]; exact hq.1 tid h
    · exact hq.1 t ht
  · dsimp only at ht
    split at ht
    · rename_i h; rw [hP t ht]; exact hq.2 tid h
    · exact hq.2 t ht

end endpointQueueLabelsAgree

namespace EndpointQueueLabelsKept

open endpointQueueLabelsAgree

/-- **The pop keeps the link labels**: the head's successor, which carries the
head's label and so the endpoint's, heads the queue. -/
theorem endpointQueuePopHead {eid : SeLe4n.ObjId} {isRecv : Bool} {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.endpointQueuePopHead eid isRecv st = .ok (tid, tcb, st')) :
    EndpointQueueLabelsKept st st' := fun ctx H => by
  unfold _root_.SeLe4n.Kernel.endpointQueuePopHead SystemState.getObject? at hStep
  cases hObj : st.objects[eid]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _
    | frame _ | pageTable _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hQ := endsOf H hObj isRecv
      cases hHead : (if isRecv then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        have hHL := hQ.1 headTid hHead
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some htcb =>
          simp only [hLookup] at hStep
          have hLinks := links H (lookupTcb_some_objects st headTid htcb hLookup)
          revert hStep
          cases hStore : SeLe4n.Model.storeObject eid _ st with
          | error e => simp
          | ok pair =>
            obtain ⟨u, st1⟩ := pair; cases u
            have I1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hStore
            have hq : queueEndsLabelled ctx (ctx.endpointLabelOf eid)
                (match htcb.queueNext with
                  | some nextTid =>
                    IntrusiveQueue.mk (some nextTid) (if isRecv = true then ep.receiveQ else ep.sendQ).tail
                  | none => IntrusiveQueue.mk none none) := by
              cases hN : htcb.queueNext with
              | none => exact ⟨fun t ht => (by simp at ht), fun t ht => (by simp at ht)⟩
              | some n =>
                refine ⟨fun t ht => ?_, fun t ht => hQ.2 t ht⟩
                simp only [Option.some.injEq] at ht
                subst ht; rw [hLinks.2 _ hN]; exact hHL
            have H1 := endpointQueueLabelsAgree.storeObject hInv hStore H
              (endpoint_entry_withQ isRecv (H _ _ hObj) hq)
            cases hNext : htcb.queueNext with
            | none =>
              simp only []
              cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks st1 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact endpointQueueLabelsAgree.storeTcbQueueLinks I1 hFinal H1 (by simp) (by simp)
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb st1 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : _root_.SeLe4n.Kernel.storeTcbQueueLinks st1 nextTid none
                    (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have I2 := storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ I1 hLink
                  have H2 := endpointQueueLabelsAgree.storeTcbQueueLinks I1 hLink H1 (by simp)
                    (links H1 (lookupTcb_some_objects st1 nextTid nextTcb hLookupNext)).2
                  cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact endpointQueueLabelsAgree.storeTcbQueueLinks I2 hFinal H2 (by simp) (by simp)

/-- **The append keeps the link labels under a labelling that gives the
appended thread the endpoint's label**: it follows the old tail, which carries
the endpoint's label. -/
theorem _root_.SeLe4n.Kernel.EndpointQueueLabelsGrowAt.endpointQueueEnqueue {eid : SeLe4n.ObjId}
    {isRecv : Bool} {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.endpointQueueEnqueue eid isRecv tid st = .ok st') :
    EndpointQueueLabelsGrowAt tid eid st st' := fun ctx hW H => by
  unfold _root_.SeLe4n.Kernel.endpointQueueEnqueue SystemState.getObject? at h
  cases hObj : st.objects[eid]? with
  | none => simp [hObj] at h
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _
    | frame _ | pageTable _ => simp [hObj] at h
    | endpoint ep =>
      simp only [hObj] at h
      have hQ := endsOf H hObj isRecv
      cases hL : lookupTcb st tid with
      | none => simp [hL] at h
      | some tcb =>
        simp only [hL] at h
        split at h
        · cases h
        split at h
        · cases h
        revert h
        cases hTail : (if isRecv then ep.receiveQ else ep.sendQ).tail with
        | none =>
          simp only []
          cases hS : SeLe4n.Model.storeObject eid _ st with
          | error e => simp
          | ok pair =>
            obtain ⟨u, st1⟩ := pair; cases u
            intro h
            have I1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS
            have H1 := endpointQueueLabelsAgree.storeObject hInv hS H
              (endpoint_entry_withQ isRecv (H _ _ hObj)
                ⟨fun t ht => by simp only [Option.some.injEq] at ht; subst ht; exact hW,
                 fun t ht => by simp only [Option.some.injEq] at ht; subst ht; exact hW⟩)
            exact endpointQueueLabelsAgree.storeTcbQueueLinks I1 h H1 (by simp) (by simp)
        | some tailTid =>
          simp only []
          have hTL := hQ.2 tailTid hTail
          cases hLT : lookupTcb st tailTid with
          | none => simp
          | some tailTcb =>
            simp only []
            have hTLinks := links H (lookupTcb_some_objects st tailTid tailTcb hLT)
            cases hS : SeLe4n.Model.storeObject eid _ st with
            | error e => simp
            | ok pair =>
              obtain ⟨u, st1⟩ := pair; cases u
              simp only []
              have I1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS
              have H1 := endpointQueueLabelsAgree.storeObject hInv hS H
                (endpoint_entry_withQ isRecv (H _ _ hObj)
                  ⟨fun t ht => hQ.1 t ht,
                   fun t ht => by simp only [Option.some.injEq] at ht; subst ht; exact hW⟩)
              cases h2 : _root_.SeLe4n.Kernel.storeTcbQueueLinks st1 tailTid tailTcb.queuePrev
                  tailTcb.queuePPrev (some tid) with
              | error e => simp
              | ok st2 =>
                simp only []
                intro h
                have I2 := storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ I1 h2
                have H2 := endpointQueueLabelsAgree.storeTcbQueueLinks I1 h2 H1 hTLinks.1
                  (fun u hu => by simp only [Option.some.injEq] at hu; subst hu; rw [hW, hTL])
                exact endpointQueueLabelsAgree.storeTcbQueueLinks I2 h H2
                  (fun u hu => by simp only [Option.some.injEq] at hu; subst hu; rw [hW, hTL])
                  (by simp)

/-- **The removal keeps the link labels**: the removed thread's neighbours,
which carry its label, are joined, and an end that named it moves to one of
them. -/
theorem endpointQueueRemoveDual {st st' : SystemState} {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    EndpointQueueLabelsKept st st' := fun ctx H => by
  unfold _root_.SeLe4n.Kernel.endpointQueueRemoveDual dualQueueRemovalEnabled dualQueueRemovalGuard SystemState.getObject? at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp
    | endpoint ep =>
      simp only []
      have hQ := endsOf H hObj isReceiveQ
      have hE := H _ _ hObj
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        have hTL := links H (lookupTcb_some_objects st tid tcb hLookup)
        have hB := fun q (hq : queueEndsLabelled ctx (ctx.endpointLabelOf endpointId) q) =>
          endpoint_entry_withQ (ep := ep) isReceiveQ hE
            (queueRemoveBoundary_labelled (tid := tid) (removed := tcb) hq hTL.1 hTL.2)
        cases hPPrev : tcb.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then ep.receiveQ else ep.sendQ) = q at hQ
          cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · rename_i hG
                have hH : q.head = some tid := by
                  simp at hG
                  exact hG.2.2.1
                have hTid := hQ.1 tid hH
                cases hStore1 : SeLe4n.Model.storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                have I1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hInv hStore1
                have H1 := endpointQueueLabelsAgree.storeObject hInv hStore1 H
                  (endpoint_entry_withQ isReceiveQ hE ⟨fun t ht => by rw [hTL.2 t ht, hTid],
                    fun t ht => hQ.2 t ht⟩)
                simp only []; cases hNext : tcb.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : SeLe4n.Model.storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have I2 := storeObject_preserves_objects_invExt' _ endpointId _ pair2 I1 hStore2
                    exact endpointQueueLabelsAgree.storeTcbQueueLinks I2 hFinal
                      (endpointQueueLabelsAgree.storeObject I1 hStore2 H1 (hB q hQ)) (by simp) (by simp)
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  have I2 := storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ I1 hLink
                  have H2 := endpointQueueLabelsAgree.storeTcbQueueLinks I1 hLink H1
                    (fun u hu => by rw [hTL.1 u hu, ← hTL.2 nextTid hNext])
                    (links H1 (lookupTcb_some_objects _ nextTid nextTcb hLookupN)).2
                  simp only []; cases hStore2 : SeLe4n.Model.storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have I3 := storeObject_preserves_objects_invExt' _ endpointId _ pair2 I2 hStore2
                    exact endpointQueueLabelsAgree.storeTcbQueueLinks I3 hFinal
                      (endpointQueueLabelsAgree.storeObject I2 hStore2 H2 (hB q hQ)) (by simp) (by simp)
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · rename_i hG
                have hP : tcb.queuePrev = some prevTid := by
                  simp at hG
                  exact hG.2.2.2
                have hPL := hTL.1 prevTid hP
                cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · rename_i _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : _root_.SeLe4n.Kernel.storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    have I1 := storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ hInv hLink0
                    have H1 := endpointQueueLabelsAgree.storeTcbQueueLinks hInv hLink0 H
                      (links H (lookupTcb_some_objects _ prevTid prevTcb hLookupP)).1
                      (fun u hu => by rw [hTL.2 u hu, hPL])
                    cases hNext : tcb.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : SeLe4n.Model.storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have I2 := storeObject_preserves_objects_invExt' _ endpointId _ pair2 I1 hStore2
                        exact endpointQueueLabelsAgree.storeTcbQueueLinks I2 hFinal
                          (endpointQueueLabelsAgree.storeObject I1 hStore2 H1 (hB q hQ)) (by simp) (by simp)
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : _root_.SeLe4n.Kernel.storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      have I2 := storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ I1 hLink1
                      have H2 := endpointQueueLabelsAgree.storeTcbQueueLinks I1 hLink1 H1
                        (fun u hu => by rw [hTL.1 u hu, ← hTL.2 nextTid hNext])
                        (links H1 (lookupTcb_some_objects _ nextTid nextTcb hLookupN)).2
                      dsimp only [hLink1]; cases hStore2 : SeLe4n.Model.storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have I3 := storeObject_preserves_objects_invExt' _ endpointId _ pair2 I2 hStore2
                        exact endpointQueueLabelsAgree.storeTcbQueueLinks I3 hFinal
                          (endpointQueueLabelsAgree.storeObject I2 hStore2 H2 (hB q hQ)) (by simp) (by simp)

end EndpointQueueLabelsKept


/-! ### The queue writes as queue-label frames -/

/-- **The pop**: no new waiter, the notification queues kept, the link labels
kept. -/
theorem QueueLabelsFrame.endpointQueuePopHead {eid : SeLe4n.ObjId} {isRecv : Bool}
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.endpointQueuePopHead eid isRecv st = .ok (tid, tcb, st')) :
    QueueLabelsFrame st st' :=
  .of_endpointFrame (RecordsEndpointFrame.endpointQueuePopHead hInv hStep)
    (EndpointQueueLabelsKept.endpointQueuePopHead hInv hStep)

/-- **The append**: a growth at the appended thread and its endpoint. -/
theorem QueueLabelsGrowFrame.endpointQueueEnqueue {eid : SeLe4n.ObjId} {isRecv : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.endpointQueueEnqueue eid isRecv tid st = .ok st') :
    QueueLabelsGrowFrame tid eid st st' :=
  have F := RecordsEndpointFrame.endpointQueueEnqueue hInv h
  ⟨(EndpointWaitersShrink.of_coreFrame F.core).growAt tid eid, .of_endpointFrame F,
    EndpointQueueLabelsGrowAt.endpointQueueEnqueue hInv h, F.invExt⟩

end SeLe4n.Kernel
