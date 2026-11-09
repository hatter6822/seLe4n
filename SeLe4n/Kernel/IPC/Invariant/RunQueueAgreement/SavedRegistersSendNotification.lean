/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegistersCapabilityDispatch
import SeLe4n.Kernel.IPC.CrossCore.InterruptDelivery

/-!
# The saved-register census over the send and notification arms

WS-ZA ZA6.26.  The `.send`, `.notificationSignal`, `.declassifySignal` and
`.notificationWait` arms of `dispatchWithCapChecked`, each read as the threads
it writes (`savedRegsWrittenFree`, at the entry's start).

* **The transitions write no saved register** (`savedRegsUnwritten`).  A send
  hands its receiver the message as a pending message, not in registers
  (`storeTcbReceiveComplete`); a signal hands its waiter the badge the same way;
  the queue pops, appends and removals write queue links, the blocks write IPC
  states and messages, the wakes and deschedules write run-queue links, the
  send-cap record writes the blocked sender's capability bits, the capability
  transfer writes CNodes and the derivation tree, the notification links are
  notification links, and the declassification record writes the audit trail.
* **The dispatch's staging names a thread blocked at the entry's start.**  The
  woken receiver's delivery (`stageWokenDelivery`) names the receive queue's
  head, the bound thread blocked on receive or the notification's head waiter,
  each read off the state the entry began from and blocked there
  (`queueHeadBlockedConsistent`, `boundDeliveryTarget?_some`,
  `notificationHeadsWakeable`), so current nowhere and resident nowhere
  (`offCoreFree_of_notReady`).  A thread with no TCB there is held by no core
  either: a current thread is active and a resident has a TCB.
* **The wait's badge return names the caller**, the executing core's current
  thread, which no other core holds (`offCoreFree_of_current`).

The arms' census follows through `savedRegsWrittenFree.census`; the call,
receive and reply arms are `SavedRegistersCallReply`'s, and the dispatch's census
over every arm is `SavedRegistersDispatch`'s.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- WS-ZA ZA6.26: **the step writes no thread's saved registers**, and the store
stays well formed. -/
def savedRegsUnwritten (pre post : SystemState) : Prop :=
  savedRegsKeptExcept (fun _ => False) pre post ∧ post.objects.invExt

namespace savedRegsUnwritten

theorem refl {st : SystemState} (h : st.objects.invExt) : savedRegsUnwritten st st :=
  ⟨.refl _, h⟩

theorem trans {a b c : SystemState} (h₁ : savedRegsUnwritten a b) (h₂ : savedRegsUnwritten b c) :
    savedRegsUnwritten a c :=
  ⟨h₁.1.trans h₂.1, h₂.2⟩

theorem savedRegs_eq {pre post : SystemState} (h : savedRegsUnwritten pre post)
    (t : SeLe4n.ThreadId) : post.savedRegs t = pre.savedRegs t :=
  h.1 t id

theorem kept {W : SeLe4n.ThreadId → Prop} {pre post : SystemState}
    (h : savedRegsUnwritten pre post) : savedRegsKeptExcept W pre post :=
  savedRegsKeptExcept.of_eq h.savedRegs_eq

theorem writtenFree {e : CoreId} {base pre post : SystemState} (h : savedRegsUnwritten pre post) :
    savedRegsWrittenFree e base pre post :=
  fun t => .inl (h.savedRegs_eq t)

/-- A slot that held no thread at `st` holds none after a step from `st` that
writes no saved register. -/
theorem noTcb {st s : SystemState} {oid : SeLe4n.ObjId} (hF : savedRegsUnwritten st s)
    (hPre : ∀ x : TCB, st.objects[oid]? ≠ some (.tcb x)) :
    ∀ x : TCB, s.objects[oid]? ≠ some (.tcb x) := fun x hx => by
  have e := hF.savedRegs_eq (SeLe4n.ThreadId.ofObjId oid)
  rw [savedRegs_eq_some_iff.mpr ⟨x, hx, rfl⟩] at e
  obtain ⟨y, hy, -⟩ := savedRegs_eq_some_iff.mp e.symm
  exact hPre y hy

/-- A thread's slot holds a thread with the same registers after a step from
`st` that writes no saved register. -/
theorem tcbAt {st s : SystemState} {tid : SeLe4n.ThreadId} {t : TCB} (hF : savedRegsUnwritten st s)
    (hPre : st.objects[tid.toObjId]? = some (.tcb t)) :
    ∃ y : TCB, s.objects[tid.toObjId]? = some (.tcb y) ∧ y.registerContext = t.registerContext := by
  have e := hF.savedRegs_eq tid
  rw [savedRegs_eq_some_iff.mpr ⟨t, hPre, rfl⟩] at e
  exact savedRegs_eq_some_iff.mp e

end savedRegsUnwritten

/-! ### The writes that hold no register -/

namespace savedRegsUnwritten

/-- A TCB rewrite that keeps the thread's saved registers. -/
theorem of_modifyTcb {st st' : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : modifyTcb st tid f = .ok st')
    (hf : ∀ x, (f x).registerContext = x.registerContext := by intro _; rfl) :
    savedRegsUnwritten st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  exact ⟨.storeObject_tcb hInv (lookupTcb_some_objects _ _ _ hL) hS (hf tcb),
    storeObject_preserves_objects_invExt _ _ _ _ hInv hS⟩

/-- A store of an object that is no thread over a slot that held none at `st`,
after a step from `st` that writes no saved register. -/
theorem of_storeObject_after {st s s' : SystemState} {oid : SeLe4n.ObjId} {obj : KernelObject}
    (hPre : ∀ x : TCB, st.objects[oid]? ≠ some (.tcb x)) (hObj : ∀ x : TCB, obj ≠ .tcb x)
    (hF : savedRegsUnwritten st s) (h : storeObject oid obj s = .ok ((), s')) :
    savedRegsUnwritten st s' :=
  hF.trans ⟨.storeObject_notTcb hF.2 (hF.noTcb hPre) h hObj,
    storeObject_preserves_objects_invExt _ _ _ _ hF.2 h⟩

/-- An endpoint stored over the slot of an endpoint at `st`. -/
theorem of_storeObject_endpoint {st s : SystemState} {oid : SeLe4n.ObjId} {ep ep' : Endpoint}
    {pair : Unit × SystemState} (hObj : st.objects[oid]? = some (.endpoint ep))
    (hF : savedRegsUnwritten st s) (h : storeObject oid (.endpoint ep') s = .ok pair) :
    savedRegsUnwritten st pair.2 := by
  obtain ⟨⟨⟩, s'⟩ := pair
  exact of_storeObject_after (fun x hx => by rw [hObj] at hx; cases hx) (fun x hx => by cases hx)
    hF h

/-- A notification stored over the slot of a notification at `st`. -/
theorem of_storeObject_notification {st s s' : SystemState} {oid : SeLe4n.ObjId}
    {n : Notification} {obj : Notification} (hN : st.getNotification? oid = some n)
    (hF : savedRegsUnwritten st s) (h : storeObject oid (.notification obj) s = .ok ((), s')) :
    savedRegsUnwritten st s' :=
  of_storeObject_after (fun x hx => by
      rw [(SystemState.getNotification?_eq_some_iff st oid n).mp hN] at hx; cases hx)
    (fun x hx => by cases hx) hF h

/-- A thread stored over its own slot with the registers it held at `st`. -/
theorem of_storeObject_tcb_after {st s s' : SystemState} {tid : SeLe4n.ThreadId} {t t' : TCB}
    (hPre : st.objects[tid.toObjId]? = some (.tcb t)) (hr : t'.registerContext = t.registerContext)
    (hF : savedRegsUnwritten st s) (h : storeObject tid.toObjId (.tcb t') s = .ok ((), s')) :
    savedRegsUnwritten st s' := by
  obtain ⟨y, hy, hyr⟩ := hF.tcbAt hPre
  exact hF.trans ⟨.storeObject_tcb hF.2 hy h (hr.trans hyr.symm),
    storeObject_preserves_objects_invExt _ _ _ _ hF.2 h⟩

theorem of_storeTcbQueueLinks {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev} {next : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    savedRegsUnwritten st st' := by
  unfold storeTcbQueueLinks at h
  exact of_modifyTcb hInv h

theorem of_storeTcbIpcStateAndMessage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {ipc : ThreadIpcState} {msg : Option IpcMessage} (hInv : st.objects.invExt)
    (h : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') : savedRegsUnwritten st st' := by
  unfold storeTcbIpcStateAndMessage at h
  exact of_modifyTcb hInv h

theorem of_storeTcbReceiveComplete {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {msg : Option IpcMessage} (hInv : st.objects.invExt)
    (h : storeTcbReceiveComplete st tid msg = .ok st') : savedRegsUnwritten st st' := by
  unfold storeTcbReceiveComplete at h
  exact of_modifyTcb hInv h

theorem of_storeTcbIpcState {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {ipc : ThreadIpcState} (hInv : st.objects.invExt)
    (h : storeTcbIpcState st tid ipc = .ok st') : savedRegsUnwritten st st' := by
  unfold storeTcbIpcState at h
  exact of_modifyTcb hInv h

/-- A wake writes the woken thread's IPC state and run-queue links. -/
theorem of_wakeThread (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : savedRegsUnwritten st (wakeThread st tid c).1 := by
  refine ⟨.of_eq fun t => ?_, wakeThread_preserves_objects_invExt st tid c hInv⟩
  rw [wakeThread_state_eq_enqueue]
  exact savedRegs_enqueueRunnableOnCore st _ tid hInv t

theorem of_removeRunnableOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : savedRegsUnwritten st (removeRunnableOnCore st tid c) :=
  ⟨.of_runLinks (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c),
    removeRunnableOnCore_objects_invExt st tid c hInv⟩

theorem of_recordSendCap (st : SystemState) (tid : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge) (grant : Bool) (hInv : st.objects.invExt) :
    savedRegsUnwritten st (recordSendCap st tid badge grant) :=
  ⟨.of_runLinks (recordSendCap_objectsAgreeOffRunLinks st tid badge grant),
    recordSendCap_objects_invExt st tid badge grant hInv⟩

/-- The notification-queue link writes rewrite two links of a thread. -/
theorem of_ntfnLinksRewritten {st s : SystemState} (h : ntfnLinksRewritten st s) :
    savedRegsUnwritten st s :=
  ⟨.of_slotsTcb fun k => by
    rcases h.2.2 k with e | ⟨t, t', h0, h1, np, nn, rfl⟩
    · exact .inl e
    · exact .inr (.inr ⟨t, _, h0, h1, rfl⟩), h.2.1⟩

theorem of_detachNtfnHead (st : SystemState) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsUnwritten st (detachNtfnHead st head next) :=
  of_ntfnLinksRewritten (detachNtfnHead_linksRewritten st head next hInv)

theorem of_linkNtfnWaiter {st st' : SystemState} {waiter : SeLe4n.ThreadId}
    {tail : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : linkNtfnWaiter st waiter tail = .ok st') : savedRegsUnwritten st st' := by
  obtain ⟨st3, h3, h4⟩ := linkNtfnWaiter_ok_cases h
  unfold storeTcbNtfnLinks at h3
  have f3 := of_modifyTcb hInv h3
  unfold relinkNtfnNext modifyTcbOpt at h4
  cases tail with
  | none => cases h4; exact f3
  | some t => exact f3.trans (of_modifyTcb f3.2 h4)

end savedRegsUnwritten

/-! ### The endpoint queues -/

/-- Popping an endpoint queue's head rewrites the endpoint and two queue links. -/
theorem endpointQueuePopHead_savedRegsUnwritten {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {st st' : SystemState} {rTid : SeLe4n.ThreadId} {rTcb : TCB} (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    savedRegsUnwritten st st' := by
  unfold endpointQueuePopHead SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hS1 : savedRegsUnwritten st pair.2 := savedRegsUnwritten.of_storeObject_endpoint hObj (.refl hObjInv) hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact hS1.trans (savedRegsUnwritten.of_storeTcbQueueLinks hInv1 hFinal)
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact (hS1.trans (savedRegsUnwritten.of_storeTcbQueueLinks hInv1 hLink)).trans
                      (savedRegsUnwritten.of_storeTcbQueueLinks hInv2 hFinal)

/-- Enqueueing on an endpoint rewrites the endpoint and at most two queue links. -/
theorem endpointQueueEnqueue_savedRegsUnwritten {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    savedRegsUnwritten st st' := by
  unfold endpointQueueEnqueue SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                intro hStep
                exact (savedRegsUnwritten.of_storeObject_endpoint hObj (.refl hObjInv) hStore).trans
                  (savedRegsUnwritten.of_storeTcbQueueLinks hInv1 hStep)
            | some tailTid =>
              cases hLookupT : lookupTcb st tailTid
              · simp [hLookupT]
              · rename_i tailTcb
                simp only [hLookupT]
                cases hStore : storeObject endpointId _ st
                · simp
                · rename_i pair
                  simp only []
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some tid)
                  · simp
                  · rename_i st2
                    simp only []
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    intro hStep
                    exact ((savedRegsUnwritten.of_storeObject_endpoint hObj (.refl hObjInv) hStore).trans
                      (savedRegsUnwritten.of_storeTcbQueueLinks hInv1 hLink1)).trans
                      (savedRegsUnwritten.of_storeTcbQueueLinks hInv2 hStep)

/-- Removing a thread from an endpoint queue rewrites the endpoint and queue
links only. -/
theorem endpointQueueRemoveDual_savedRegsUnwritten {st st' : SystemState} {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    savedRegsUnwritten st st' := by
  have epStore := @savedRegsUnwritten.of_storeObject_endpoint
  unfold endpointQueueRemoveDual dualQueueRemovalEnabled dualQueueRemovalGuard SystemState.getObject? at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp
    | endpoint ep =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        cases hPPrev : tcb.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
          -- `v0.35.59`: `cases pprev` precedes the `split`.  With the two
          -- preconditions collapsed into `dualQueueRemovalEnabled`, unfolding the
          -- guard exposes the guard's own `match pprev` *inside* the `if`
          -- condition, and `split` takes that before the `if` -- so the
          -- constructor split has to come first.
          cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []; cases hNext : tcb.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have f1 := epStore hObj (savedRegsUnwritten.refl hInv) hStore1
                    have f2 := epStore hObj f1 hStore2
                    exact f2.trans (savedRegsUnwritten.of_storeTcbQueueLinks f2.2 hFinal)
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []; cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have f1 := epStore hObj (savedRegsUnwritten.refl hInv) hStore1
                    have f2 := f1.trans (savedRegsUnwritten.of_storeTcbQueueLinks f1.2 hLink)
                    have f3 := epStore hObj f2 hStore2
                    exact f3.trans (savedRegsUnwritten.of_storeTcbQueueLinks f3.2 hFinal)
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · -- split introduced heq✝ : (if ... then .error else match storeTcbQueueLinks ... with ...) = .ok st''✝
                  -- and the goal uses st''✝. Resolve heq✝ to extract the actual state.
                  rename_i _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    -- Now stAp = stPrev, goal uses stPrev
                    cases hNext : tcb.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have f1 := savedRegsUnwritten.of_storeTcbQueueLinks hInv hLink0
                        have f2 := epStore hObj f1 hStore2
                        exact f2.trans (savedRegsUnwritten.of_storeTcbQueueLinks f2.2 hFinal)
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]; cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have f1 := savedRegsUnwritten.of_storeTcbQueueLinks hInv hLink0
                        have f2 := f1.trans (savedRegsUnwritten.of_storeTcbQueueLinks f1.2 hLink1)
                        have f3 := epStore hObj f2 hStore2
                        exact f3.trans (savedRegsUnwritten.of_storeTcbQueueLinks f3.2 hFinal)

/-! ### The send -/

/-- The per-core send writes no saved register: the rendezvous pops the
receiver, hands it the message as a pending message and wakes it; the block
appends the sender, stores its state, deschedules it and records its
capability's bits. -/
theorem endpointSendDualOnCore_savedRegsUnwritten (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload) (c : CoreId) {st : SystemState}
    (hInv : st.objects.invExt) :
    savedRegsUnwritten st (endpointSendDualOnCore endpointId sender payload c st).1 := by
  unfold endpointSendDualOnCore
  split
  · split
    · split
      · exact .refl hInv
      · split
        · exact .refl hInv
        · rename_i receiver _ st1 hPop
          split
          · exact .refl hInv
          · rename_i st2 hRecv
            have h1 := endpointQueuePopHead_savedRegsUnwritten hInv hPop
            have h2 := h1.trans (savedRegsUnwritten.of_storeTcbReceiveComplete h1.2 hRecv)
            exact h2.trans (savedRegsUnwritten.of_wakeThread st2 receiver c h2.2)
    · split
      · exact .refl hInv
      · rename_i st1 hEnq
        split
        · exact .refl hInv
        · rename_i st2 hBlk
          have h1 := endpointQueueEnqueue_savedRegsUnwritten hInv hEnq
          have h2 := h1.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h1.2 hBlk)
          have h3 := h2.trans (savedRegsUnwritten.of_removeRunnableOnCore st2 sender c h2.2)
          exact h3.trans (savedRegsUnwritten.of_recordSendCap _ sender _ _ h3.2)
  · split <;> exact .refl hInv

/-- The capability transfer writes CNodes and the derivation tree alone. -/
theorem receiveTransferCaps_savedRegsUnwritten
    {req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)} {endpointId : SeLe4n.ObjId}
    {target? : Option (TCB × Option CSpaceAddr)} {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt) (h : receiveTransferCaps req endpointId target? st = .ok (summary, st')) :
    savedRegsUnwritten st st' := by
  obtain ⟨stR, _, hO, -, -, hOr⟩ := receiveTransferCaps_frame h
  have h1 : savedRegsUnwritten st stR :=
    ⟨.of_objects_eq hO, by rw [hO]; exact hInv⟩
  rcases hOr with rfl | ⟨rtcb, slot?, hU⟩
  · exact h1
  · exact h1.trans ⟨.of_map fun x =>
      TCB.map_proj_of_map_withoutLinks_eq TCB.registerContext
        (ipcUnwrapCaps_getTcb?_eq _ _ _ _ _ _ _ x h1.2 hU),
      ipcUnwrapCaps_preserves_objects_invExt _ _ _ _ _ _ _ h1.2 hU⟩

/-- The send with capability transfer writes no saved register. -/
theorem endpointSendDualWithCapsOnCore_savedRegsUnwritten (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload) (c : CoreId)
    {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st
      (endpointSendDualWithCapsOnCore endpointId sender payload c st).1 := by
  have h0 := endpointSendDualOnCore_savedRegsUnwritten endpointId sender payload c hInv
  unfold endpointSendDualWithCapsOnCore
  generalize endpointSendDualOnCore endpointId sender payload c st = r at h0
  obtain ⟨st1, r⟩ := r
  cases r with
  | error _ => exact h0
  | ok _ =>
    dsimp only
    repeat' split
    all_goals first
      | exact h0
      | (rename_i hU; exact h0.trans (receiveTransferCaps_savedRegsUnwritten h0.2 hU))

/-- The live checked send writes no saved register. -/
theorem endpointSendCrossCoreDispatchChecked_savedRegsUnwritten (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload c st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact endpointSendDualWithCapsOnCore_savedRegsUnwritten _ _ _ _ hInv
  · exact .refl hInv

/-! ### The notifications -/

/-- The per-core signal writes no saved register: the head waiter is handed
the badge as a pending message, unlinked and woken, or the badge is merged into
the notification. -/
theorem notificationSignalOnCore_savedRegsUnwritten (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (notificationSignalOnCore notificationId badge c st).1 := by
  unfold notificationSignalOnCore
  split
  · rename_i ntfn hN
    split
    · try dsimp only
      split
      · exact .refl hInv
      · rename_i st1 hS
        have h1 := savedRegsUnwritten.of_storeObject_notification hN (.refl hInv) hS
        try dsimp only
        split
        · exact .refl hInv
        · rename_i st2 hT
          have h2 := h1.trans (savedRegsUnwritten.of_storeTcbIpcStateAndMessage h1.2 hT)
          exact (h2.trans (savedRegsUnwritten.of_detachNtfnHead st2 _ _ h2.2)).trans
            (savedRegsUnwritten.of_wakeThread _ _ c (detachNtfnHead_linksRewritten _ _ _ h2.2).2.1)
    · try dsimp only
      split
      · exact .refl hInv
      · rename_i st1 hS
        exact savedRegsUnwritten.of_storeObject_notification hN (.refl hInv) hS
  · split <;> exact .refl hInv

/-- The bound signal writes no saved register: the bound thread is removed from
its endpoint, handed the badge as a pending message and woken, or the ordinary
signal runs. -/
theorem notificationSignalBoundOnCore_savedRegsUnwritten (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (notificationSignalBoundOnCore notificationId badge c st).1 := by
  unfold notificationSignalBoundOnCore
  split
  · try dsimp only
    split
    · exact .refl hInv
    · rename_i st1 hR
      have h1 := endpointQueueRemoveDual_savedRegsUnwritten hInv hR
      split
      · exact .refl hInv
      · rename_i st2 hT
        have h2 := h1.trans (savedRegsUnwritten.of_storeTcbReceiveComplete h1.2 hT)
        exact h2.trans (savedRegsUnwritten.of_wakeThread st2 _ c h2.2)
  · exact notificationSignalOnCore_savedRegsUnwritten _ _ _ hInv

/-- The checked signal writes no saved register. -/
theorem notificationSignalBoundCrossCoreDispatchChecked_savedRegsUnwritten
    (ctx : LabelingContext) (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId
      signaler badge c st).1 := by
  unfold notificationSignalBoundCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact notificationSignalBoundOnCore_savedRegsUnwritten _ _ _ hInv
    | exact .refl hInv

/-- The declassifying signal writes no saved register: the bound signal, then
the audit trail. -/
theorem notificationSignalDeclassifiedCrossCoreDispatch_savedRegsUnwritten
    {ctx : GenericLabelingContext} {declPolicy : DeclassificationPolicy}
    {notificationId : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st st' : SystemState} {sgi : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy notificationId badge c st
      = (st', .ok sgi)) : savedRegsUnwritten st st' := by
  have hF := notificationSignalDeclassifiedOnCore_frame ctx declPolicy notificationId badge c
    st st' sgi h
  have h1 := notificationSignalBoundOnCore_savedRegsUnwritten notificationId badge c hInv
  have hO : st'.objects = (notificationSignalBoundOnCore notificationId badge c st).1.objects := by
    rw [hF]
  exact h1.trans ⟨.of_objects_eq hO, by rw [hO]; exact h1.2⟩

/-- The per-core wait writes no saved register: the badge's consumption clears
the notification and readies the caller; the block appends the caller, stores
its state, links it and deschedules it. -/
theorem notificationWaitOnCore_savedRegsUnwritten (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (c : CoreId) {st : SystemState} (hInv : st.objects.invExt) :
    savedRegsUnwritten st (notificationWaitOnCore notificationId waiter c st).1 := by
  unfold notificationWaitOnCore
  split
  · rename_i ntfn hN
    split
    · try dsimp only
      split
      · exact .refl hInv
      · rename_i st1 hS
        have h1 := savedRegsUnwritten.of_storeObject_notification hN (.refl hInv) hS
        split
        · exact .refl hInv
        · rename_i st2 hT
          exact h1.trans (savedRegsUnwritten.of_storeTcbIpcState h1.2 hT)
    · split
      · exact .refl hInv
      · rename_i tcb hL
        split
        · exact .refl hInv
        · dsimp only
          split
          · exact .refl hInv
          · rename_i st1 hS
            have h1 := savedRegsUnwritten.of_storeObject_notification hN (.refl hInv) hS
            split
            · exact .refl hInv
            · rename_i st2 hT
              have h2 : savedRegsUnwritten st st2 := by
                unfold storeTcbIpcStateAndMessage_fromTcb at hT
                revert hT
                cases hSt : storeObject waiter.toObjId _ st1 with
                | error _ => intro h; cases h
                | ok p =>
                  obtain ⟨⟨⟩, s⟩ := p
                  intro h; cases h
                  refine savedRegsUnwritten.of_storeObject_tcb_after
                    (lookupTcb_some_objects _ _ _ hL) ?_ h1 hSt
                  rfl
              split
              · exact .refl hInv
              · rename_i st4 hLink
                have h3 := h2.trans (savedRegsUnwritten.of_linkNtfnWaiter h2.2 hLink)
                exact h3.trans (savedRegsUnwritten.of_removeRunnableOnCore _ waiter c h3.2)
  · split <;> exact .refl hInv

/-- The checked wait writes no saved register. -/
theorem notificationWaitCrossCoreDispatchChecked_savedRegsUnwritten (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (c : CoreId) {st : SystemState}
    (hInv : st.objects.invExt) :
    savedRegsUnwritten st
      (notificationWaitCrossCoreDispatchChecked ctx notificationId waiter c st).1 := by
  unfold notificationWaitCrossCoreDispatchChecked
  split
  · exact notificationWaitOnCore_savedRegsUnwritten _ _ _ hInv
  · exact .refl hInv

/-- The woken receiver's stash clear rewrites one field of a thread. -/
theorem clearWokenReceiverStash_savedRegsUnwritten {w : Option SeLe4n.ThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : clearWokenReceiverStash w st = .ok ((), st')) : savedRegsUnwritten st st' := by
  unfold clearWokenReceiverStash at h
  split at h
  · cases h; exact .refl hInv
  · split at h
    · rename_i rTcb hT
      split at h
      · refine savedRegsUnwritten.of_storeObject_tcb_after
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) ?_ (.refl hInv) h
        rfl
      · cases h; exact .refl hInv
    · cases h; exact .refl hInv

/-! ### The dispatch's staging -/

/-- **A delivered message's staging writes the receiver alone**: its frame and
its message, then the overflow words into its IPC buffer, which is memory. -/
theorem stageDeliveredMessage_savedRegsKeptExcept (st : SystemState) (tid : SeLe4n.ThreadId)
    (n : Nat) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (· = tid) st (Architecture.stageDeliveredMessage st tid n) ∧
      (Architecture.stageDeliveredMessage st tid n).objects.invExt := by
  unfold Architecture.stageDeliveredMessage
  split
  · split
    · split
      · unfold Architecture.writeDeliveredFrameToTcb
        refine ⟨(savedRegsKeptExcept.updateTcb_written (W := (· = tid)) _ tid _ hInv rfl).trans
          (.of_objects_eq (Architecture.recordPhysicalWrites_objects _ _)), ?_⟩
        rw [Architecture.recordPhysicalWrites_objects]
        exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv
      · exact ⟨.refl _, hInv⟩
    · exact ⟨.refl _, hInv⟩
  · exact ⟨.refl _, hInv⟩

/-- **A return frame's staging writes its thread alone.** -/
theorem writeReturnFrameToTcb_savedRegsKeptExcept (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (· = tid) st (Architecture.writeReturnFrameToTcb st tid f) :=
  savedRegsKeptExcept.updateTcb_written (W := (· = tid)) _ tid _ hInv rfl

/-- **A woken thread's delivery writes that thread alone**, so it writes only
threads free at `base` when the thread it names is. -/
theorem stageWokenDelivery_savedRegsWrittenFree {e : CoreId} {base s : SystemState}
    {w : Option SeLe4n.ThreadId} (n : Nat) (hInv : s.objects.invExt)
    (hF : ∀ t, w = some t → offCoreFree e base t) :
    savedRegsWrittenFree e base s (Architecture.stageWokenDelivery s w n) ∧
      (Architecture.stageWokenDelivery s w n).objects.invExt := by
  cases w with
  | none => exact ⟨.refl _, hInv⟩
  | some t =>
    obtain ⟨k, i⟩ := stageDeliveredMessage_savedRegsKeptExcept s t n hInv
    exact ⟨.of_kept k fun _ h => h ▸ hF t rfl, i⟩

/-! ### The threads the staging names -/

/-- WS-ZA ZA6.26: **a thread with no ready TCB is held by no core**: a thread
with no TCB is current nowhere (a current thread is active) and resident
nowhere (a resident has a TCB); a blocked one is current nowhere and resident
nowhere (`offCoreFree_of_blocked`). -/
theorem offCoreFree_of_notReady {e : CoreId} {st : SystemState} {t : SeLe4n.ThreadId}
    (hD : st.currentDequeuedUnique) (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (h : ∀ x, st.getTcb? t = some x → x.ipcState ≠ .ready) : offCoreFree e st t := by
  cases hT : st.getTcb? t with
  | some x =>
    exact offCoreFree_of_blocked (blockedCurrentNowhere_of_currentDequeuedUnique hD) hBNR hT
      (h x hT)
  | none =>
    intro d _
    refine ⟨fun hc => ?_, fun hr => ?_⟩
    · obtain ⟨x, hx, -⟩ := hD.currentActive d t hc
      rw [hT] at hx; cases hx
    · have hS := hRT d t hr
      rw [hT] at hS; cases hS

/-- **The receive queue's head is held by no core**: it is blocked. -/
theorem offCoreFree_of_receiveHead {e : CoreId} {st : SystemState} {epId : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} (hD : st.currentDequeuedUnique) (hQ : queueHeadBlockedConsistent st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (h : (st.getEndpoint? epId).bind (·.receiveQ.head) = some t) : offCoreFree e st t := by
  cases hE : st.getEndpoint? epId with
  | none => rw [hE] at h; cases h
  | some ep =>
    rw [hE] at h
    exact offCoreFree_of_notReady hD hRT hBNR fun x hx =>
      endpointWaiter_notReady (q := true) hQ hE (by simpa [endpointWaitQueue] using h) hx

/-- **The bound thread a signal delivers to is held by no core**: it is blocked
on receive. -/
theorem offCoreFree_of_boundTarget {e : CoreId} {st : SystemState} {nid : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} (hD : st.currentDequeuedUnique) (hRT : st.residentsHaveTcbs)
    (hBNR : st.blockedNotResident) (h : (boundDeliveryTarget? st nid).map (·.1) = some t) :
    offCoreFree e st t := by
  cases hB : boundDeliveryTarget? st nid with
  | none => rw [hB] at h; cases h
  | some p =>
    obtain ⟨t', epId⟩ := p
    rw [hB] at h; cases h
    obtain ⟨tcb, hT, hS⟩ := boundDeliveryTarget?_some st nid _ epId hB
    exact offCoreFree_of_notReady hD hRT hBNR fun x hx => by
      rw [hT] at hx; cases hx; rw [hS]; exact fun h => by cases h

/-- **A notification's head waiter is held by no core**: it is blocked. -/
theorem offCoreFree_of_signalWaiter {e : CoreId} {st : SystemState} {nid : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} (hD : st.currentDequeuedUnique) (hNH : notificationHeadsWakeable st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (h : notificationSignalWaiter? st nid = some t) : offCoreFree e st t := by
  unfold notificationSignalWaiter? at h
  split at h
  · rename_i ntfn hN
    obtain ⟨-, x, hx, hb⟩ := hNH nid ntfn hN t h
    exact offCoreFree_of_notReady hD hRT hBNR fun y hy => by
      rw [hx] at hy; cases hy; exact hb
  · cases h

/-! ### The arms -/

/-- WS-ZA ZA6.26: **the send arm writes only the woken receiver**: the checked
send and the stash clear write no saved register, and the delivery's staging
names the receive queue's head at the entry's start, which is blocked there. -/
theorem sendArm_savedRegsWrittenFree {ctx : LabelingContext} {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {payload : SendPayload} {ec e : CoreId}
    {st s1 s2 : SystemState} {r : CapTransferSummary × Option (CoreId × Concurrency.SgiKind)}
    (n : Nat) (P : SyscallArmPremises st ec tid) (hRT : st.residentsHaveTcbs)
    (hBNR : st.blockedNotResident)
    (hSend : endpointSendCrossCoreDispatchChecked ctx epId tid payload ec st = (s1, .ok r))
    (hClr : clearWokenReceiverStash ((st.getEndpoint? epId).bind (·.receiveQ.head)) s1
      = .ok ((), s2)) :
    savedRegsWrittenFree e st st (Architecture.stageWokenDelivery s2
      ((st.getEndpoint? epId).bind (·.receiveQ.head)) n) := by
  have h1 := endpointSendCrossCoreDispatchChecked_savedRegsUnwritten ctx epId tid payload ec
    P.objInv
  rw [hSend] at h1
  have h2 := h1.trans (clearWokenReceiverStash_savedRegsUnwritten h1.2 hClr)
  exact h2.writtenFree.trans (stageWokenDelivery_savedRegsWrittenFree n h2.2 fun _ h =>
    offCoreFree_of_receiveHead P.dequeued P.queueHeads hRT hBNR h).1

/-- WS-ZA ZA6.26: **a signal arm writes only the threads it wakes**: the signal
and the stash clear write no saved register, and the two stagings name the
bound thread blocked on receive and the notification's head waiter at the
entry's start, both blocked there. -/
theorem signalArm_savedRegsWrittenFree {nid : SeLe4n.ObjId}
    {e : CoreId} {st s1 s2 : SystemState} (P : EntryPremises st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident) (h1 : savedRegsUnwritten st s1)
    (hClr : clearWokenReceiverStash ((boundDeliveryTarget? st nid).map (·.1)) s1 = .ok ((), s2)) :
    savedRegsWrittenFree e st st (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery s2 ((boundDeliveryTarget? st nid).map (·.1)) 0)
      (notificationSignalWaiter? st nid) 0) := by
  have h2 := h1.trans (clearWokenReceiverStash_savedRegsUnwritten h1.2 hClr)
  obtain ⟨w1, i1⟩ := stageWokenDelivery_savedRegsWrittenFree (e := e) (base := st) 0 h2.2
    fun _ h => offCoreFree_of_boundTarget P.dequeued hRT hBNR h
  exact (h2.writtenFree.trans w1).trans (stageWokenDelivery_savedRegsWrittenFree 0 i1 fun _ h =>
    offCoreFree_of_signalWaiter P.dequeued P.ntfnHeads hRT hBNR h).1

/-- The checked signal arm. -/
theorem notificationSignalArm_savedRegsWrittenFree {ctx : LabelingContext} {nid : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {badge : SeLe4n.Badge} {ec e : CoreId} {st s1 s2 : SystemState}
    {r : Option (CoreId × Concurrency.SgiKind)} (P : SyscallArmPremises st ec tid)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hSig : notificationSignalBoundCrossCoreDispatchChecked ctx nid tid badge ec st = (s1, .ok r))
    (hClr : clearWokenReceiverStash ((boundDeliveryTarget? st nid).map (·.1)) s1 = .ok ((), s2)) :
    savedRegsWrittenFree e st st (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery s2 ((boundDeliveryTarget? st nid).map (·.1)) 0)
      (notificationSignalWaiter? st nid) 0) := by
  have h1 := notificationSignalBoundCrossCoreDispatchChecked_savedRegsUnwritten ctx nid tid badge
    ec P.objInv
  rw [hSig] at h1
  exact signalArm_savedRegsWrittenFree P.toEntryPremises hRT hBNR h1 hClr

/-- The declassifying signal arm. -/
theorem declassifySignalArm_savedRegsWrittenFree {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {nid : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {badge : SeLe4n.Badge} {ec e : CoreId} {st s1 s2 : SystemState}
    {r : Option (CoreId × Concurrency.SgiKind)} (P : SyscallArmPremises st ec tid)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hSig : notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy nid badge ec st
      = (s1, .ok r))
    (hClr : clearWokenReceiverStash ((boundDeliveryTarget? st nid).map (·.1)) s1 = .ok ((), s2)) :
    savedRegsWrittenFree e st st (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery s2 ((boundDeliveryTarget? st nid).map (·.1)) 0)
      (notificationSignalWaiter? st nid) 0) :=
  signalArm_savedRegsWrittenFree P.toEntryPremises hRT hBNR
    (notificationSignalDeclassifiedCrossCoreDispatch_savedRegsUnwritten P.objInv hSig) hClr

/-- WS-ZA ZA6.32: **the interrupt step writes only the threads its signal
wakes**: seL4's `handleInterrupt` signals the bound notification
(`interruptSignal`), whose signal and stash clear write no saved register and
whose two stagings name the bound thread blocked on receive and the
notification's head waiter, both blocked at the entry's start; the mask writes
the machine's mask words and the physical-write ledger only. -/
theorem handleInterruptOnCore_savedRegsWrittenFree {e : CoreId} (st : SystemState) (c : CoreId)
    (line : Nat) (E : EntryPremises st) (hRT : st.residentsHaveTcbs)
    (hBNR : st.blockedNotResident) :
    savedRegsWrittenFree e st st (handleInterruptOnCore st c line) := by
  have hM : ∀ s, savedRegsWrittenFree e st st s →
      savedRegsWrittenFree e st st (Architecture.setInterruptLineMask s line true) :=
    fun _ hs t => hs t
  have h1 := fun ntfn badge => notificationSignalBoundOnCore_savedRegsUnwritten ntfn badge c E.objInv
  unfold handleInterruptOnCore
  split
  · exact hM _ (interruptSignal_of (P := savedRegsWrittenFree e st st) _ _ c st (h1 _ _).writtenFree
      fun _ _ _ hClr => signalArm_savedRegsWrittenFree E hRT hBNR (h1 _ _) hClr)
  · exact hM _ (.refl _)

/-- …and so does the raw step. -/
theorem interruptEntryStep_savedRegsWrittenFree {e : CoreId} (st : SystemState)
    (coreId intId : UInt64) (E : EntryPremises st) (hRT : st.residentsHaveTcbs)
    (hBNR : st.blockedNotResident) :
    savedRegsWrittenFree e st st (interruptEntryStep st coreId intId) :=
  interruptEntryStep_of (P := savedRegsWrittenFree e st st) st coreId intId (.refl _)
    (fun c _ _ => handleInterruptOnCore_savedRegsWrittenFree st c _ E hRT hBNR)

/-- WS-ZA ZA6.26: **the wait arm writes only the caller**: the checked wait
writes no saved register, and a consumed badge is staged into the caller, the
executing core's current thread, which no other core holds. -/
theorem notificationWaitArm_savedRegsWrittenFree {ctx : LabelingContext} {nid : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {st s1 : SystemState}
    {r : Except KernelError (Option SeLe4n.Badge)} (f : Architecture.SyscallReturnFrame)
    (P : SyscallArmPremises st ec tid) (hN : st.currentNotResidentElsewhere)
    (hW : notificationWaitCrossCoreDispatchChecked ctx nid tid ec st = (s1, r)) :
    savedRegsWrittenFree ec st st s1 ∧
      savedRegsWrittenFree ec st st (Architecture.writeReturnFrameToTcb s1 tid f) := by
  have h1 := notificationWaitCrossCoreDispatchChecked_savedRegsUnwritten ctx nid tid ec P.objInv
  rw [hW] at h1
  exact ⟨h1.writtenFree, h1.writtenFree.trans (.of_kept
    (writeReturnFrameToTcb_savedRegsKeptExcept s1 tid f h1.2) fun _ h => h ▸
      offCoreFree_of_current P.current (currentsUnique_of_dequeuedUnique P.dequeued) hN)⟩

end SeLe4n.Kernel
