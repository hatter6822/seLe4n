-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core

/-!
# What the IPC writes do to reply views (WS-ZA ZA4.6)

The reply-waiter queues are consistent over the store's reply views
(`SystemState.replyWaitersConsistent`), and a view reads five fields of a TCB:
the server its IPC state names and its four reply-waiter codes.  This module
states what each primitive write does to the views: an object store replaces
one slot's view, a TCB write whose function acts on views as `gv` maps that
slot by `gv`, and an IPC-state store sets the thread's server to the one the
new state names.  A step that writes none of the five fields keeps every view.
-/

namespace SeLe4n.Model.SystemState

open SeLe4n
open SeLe4n.Kernel
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **An object store replaces one slot's view.** -/
theorem replyViews_storeObject {st st' : SystemState} {k : ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k obj st = .ok ((), st')) (x : ObjId) :
    st'.replyViews x = if k = x then objReplyView (some obj) else st.replyViews x := by
  unfold storeObject at h; cases h
  unfold replyViews getObject?
  simp only [RHTable_getElem?_eq_get?]
  split
  · rename_i hx; subst hx; rw [RHTable.getElem?_insert_self _ _ _ hInv]
  · rename_i hx; rw [RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb)) hInv]

/-- **A TCB stored over a TCB maps that thread's view.** -/
theorem replyViews_storeObject_tcb {st st' : SystemState} {t : ThreadId} {old new : TCB}
    {gv : ReplyView → ReplyView} (hInv : st.objects.invExt)
    (h : storeObject t.toObjId (.tcb new) st = .ok ((), st'))
    (hOld : st.objects[t.toObjId]? = some (.tcb old)) (hv : new.replyView = gv old.replyView) :
    st'.replyViews = ReplyViews.mapAt st.replyViews t gv := by
  funext x
  rw [replyViews_storeObject hInv h x]
  unfold ReplyViews.mapAt
  split
  · rename_i hx; subst hx; rw [replyViews_of_tcb hOld]; simp [hv]
  · rfl

/-- **A TCB rewrite through `modifyTcb` that acts on views as `gv` maps the
thread's view by `gv`.** -/
theorem replyViews_modifyTcb {st st' : SystemState} {t : ThreadId} {f : TCB → TCB}
    {gv : ReplyView → ReplyView} (hInv : st.objects.invExt) (h : modifyTcb st t f = .ok st')
    (hf : ∀ x, (f x).replyView = gv x.replyView) :
    st'.replyViews = ReplyViews.mapAt st.replyViews t gv := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  exact replyViews_storeObject_tcb hInv hS (lookupTcb_some_objects st t tcb hL) (hf tcb)

/-- A `modifyTcb` that keeps every reply view field keeps the views. -/
theorem replyViews_modifyTcb_eq {st st' : SystemState} {t : ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : modifyTcb st t f = .ok st')
    (hf : ∀ x, (f x).replyView = x.replyView) : st'.replyViews = st.replyViews := by
  rw [replyViews_modifyTcb hInv h (gv := id) hf]
  funext x; unfold ReplyViews.mapAt; split <;> simp

/-- The server an IPC state names. -/
@[inline] def ipcServer? : ThreadIpcState → Option ThreadId
  | .blockedOnReply _ (some s) => some s
  | _ => none

theorem blockingServer?_eq_ipcServer? (t : TCB) : t.blockingServer? = ipcServer? t.ipcState := by
  unfold TCB.blockingServer? ipcServer?; rfl

/-- **An IPC-state store sets the thread's server to the one the state names.** -/
theorem replyViews_storeTcbIpcState {st st' : SystemState} {t : ThreadId} {s : ThreadIpcState}
    (hInv : st.objects.invExt) (h : storeTcbIpcState st t s = .ok st') :
    st'.replyViews = ReplyViews.setServer st.replyViews t (ipcServer? s) :=
  replyViews_modifyTcb hInv h (fun x => by
    simp only [TCB.replyView, blockingServer?_eq_ipcServer?, TCB.ipcState_setIpcState])

theorem replyViews_storeTcbIpcStateAndMessage {st st' : SystemState} {t : ThreadId}
    {s : ThreadIpcState} {m : Option IpcMessage}
    (hInv : st.objects.invExt) (h : storeTcbIpcStateAndMessage st t s m = .ok st') :
    st'.replyViews = ReplyViews.setServer st.replyViews t (ipcServer? s) :=
  replyViews_modifyTcb hInv h (fun x => by
    simp only [TCB.replyView, blockingServer?_eq_ipcServer?, TCB.ipcState_setIpcState])

/-- **A store of an object with no view over a slot with none keeps the views.** -/
theorem replyViews_storeObject_eq {st st' : SystemState} {k : ObjId} {obj : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k obj st = .ok ((), st'))
    (hOld : st.replyViews k = none) (hNew : objReplyView (some obj) = none) :
    st'.replyViews = st.replyViews := by
  funext x
  rw [replyViews_storeObject hInv h x]
  split
  · rename_i hx; subst hx; rw [hNew, hOld]
  · rfl

theorem replyViews_storeTcbQueueLinks {st st' : SystemState} {t : ThreadId}
    {prev : Option ThreadId} {pprev : Option QueuePPrev} {next : Option ThreadId}
    (hInv : st.objects.invExt) (h : storeTcbQueueLinks st t prev pprev next = .ok st') :
    st'.replyViews = st.replyViews :=
  replyViews_modifyTcb_eq hInv h (fun _ => rfl)

@[simp] theorem replyViews_withScheduler (s : SystemState) (sch : SchedulerState) :
    ({ s with scheduler := sch } : SystemState).replyViews = s.replyViews := rfl

/-- **A rewrite replaces one slot's view.** -/
theorem replyViews_rewriteObject (st : SystemState) (k : ObjId) (obj : KernelObject)
    (hA : st.rewriteAdmissible k obj) (hInv : st.objects.invExt) (x : ObjId) :
    (st.rewriteObject k obj hA).replyViews x =
      if k = x then objReplyView (some obj) else st.replyViews x := by
  unfold replyViews getObject?
  split
  · rename_i hx; subst hx; rw [rewriteObject_objects_self _ _ _ _ hInv]
  · rename_i hx; rw [rewriteObject_objects_ne _ _ _ _ _ hx hInv]

/-- A view whose server already is `srv` is kept by `setServer`. -/
theorem _root_.SeLe4n.Model.ReplyViews.setServer_of_server {V : ReplyViews} {t : ThreadId}
    {srv : Option ThreadId} (h : ∀ v, V t.toObjId = some v → v.server = srv) :
    V.setServer t srv = V := by
  funext x; unfold ReplyViews.setServer ReplyViews.mapAt
  split
  · rename_i hx; subst hx
    cases hv : V t.toObjId with
    | none => rfl
    | some v => simp only [Option.map_some]; rw [← h v hv]
  · rfl

/-- **A wake keeps the views of a thread with no server**: the enqueue's
`.ready` mark writes the one view field it names, which is already clear. -/
theorem enqueueRunnableOnCore_replyViews_eq (st : SystemState) (c : CoreId) (tid : ThreadId)
    (hInv : st.objects.invExt) (hS : ∀ v, st.replyViews tid.toObjId = some v → v.server = none) :
    (enqueueRunnableOnCore st c tid).replyViews = st.replyViews := by
  unfold enqueueRunnableOnCore
  split
  · rename_i tcb hT _
    split
    · rfl
    · dsimp only
      rw [replyViews_withScheduler, runEnqueueAdmitted_replyViews_eq]
      have hO := (getTcb?_eq_some_iff st tid tcb).1 hT
      have hSv : tcb.blockingServer? = none := hS _ (replyViews_of_tcb hO)
      funext x
      rw [replyViews_rewriteObject _ _ _ _ hInv]
      split
      · rename_i hx; subst hx
        rw [replyViews_of_tcb hO, objReplyView_tcb]
        simp only [TCB.replyView, TCB.blockingServer?, TCB.ipcState_setIpcState] at hSv ⊢
        rw [hSv]
      · rfl
  · rfl

theorem wakeThread_replyViews_eq (st : SystemState) (tid : ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) (hS : ∀ v, st.replyViews tid.toObjId = some v → v.server = none) :
    (wakeThread st tid c).1.replyViews = st.replyViews :=
  enqueueRunnableOnCore_replyViews_eq st _ tid hInv hS

theorem runUnlinkLinks_replyViews_eq (st : SystemState) (t : ThreadId) (pv nx bpv bnx : Nat) :
    (st.runUnlinkLinks t pv nx bpv bnx).replyViews = st.replyViews := by
  unfold runUnlinkLinks; dsimp only
  rw [mapTcbInPlace_replyViews_eq _ _ ?h1, updateTcbAtCode_replyViews_eq _ _ ?h2,
    updateTcbAtCode_replyViews_eq _ _ ?h3, updateTcbAtCode_replyViews_eq _ _ ?h4,
    updateTcbAtCode_replyViews_eq _ _ ?h5]
  all_goals intro x; rfl

theorem runRemoveOnCore_replyViews_eq (st : SystemState) (c : CoreId) (t : ThreadId) :
    (st.runRemoveOnCore c t).replyViews = st.replyViews := by
  unfold runRemoveOnCore; dsimp only
  rw [replyViews_withScheduler]
  split
  · rw [replyViews_withScheduler, runUnlinkLinks_replyViews_eq]
  · rfl

theorem removeRunnableOnCore_replyViews_eq (st : SystemState) (tid : ThreadId) (c : CoreId) :
    (removeRunnableOnCore st tid c).replyViews = st.replyViews := by
  unfold removeRunnableOnCore runDescheduleOnCore; dsimp only
  rw [replyViews_withScheduler, runRemoveOnCore_replyViews_eq]

/-! Reply-object stores and the TCB writes beside them (the reply-object link,
the stash, the frame splice) touch no reply view. -/

theorem replyViews_of_getReply {st : SystemState} {rid : ReplyId} {r : Reply}
    (h : st.getReply? rid = some r) : st.replyViews rid.toObjId = none := by
  unfold replyViews getObject?; rw [(getReply?_eq_some_iff st rid r).1 h]; rfl

theorem replyViews_storeReply_eq {st st' : SystemState} {rid : ReplyId} {r r' : Reply}
    (hInv : st.objects.invExt) (hOld : st.getReply? rid = some r)
    (h : storeObject rid.toObjId (.reply r') st = .ok ((), st')) :
    st'.replyViews = st.replyViews :=
  replyViews_storeObject_eq hInv h (replyViews_of_getReply hOld) rfl

theorem replyViews_storeTcb_eq {st st' : SystemState} {t : ThreadId} {old new : TCB}
    (hInv : st.objects.invExt) (hOld : st.getTcb? t = some old)
    (h : storeObject t.toObjId (.tcb new) st = .ok ((), st'))
    (hv : new.replyView = old.replyView) : st'.replyViews = st.replyViews := by
  rw [replyViews_storeObject_tcb hInv h ((getTcb?_eq_some_iff st t old).1 hOld) (gv := id) hv]
  funext x; unfold ReplyViews.mapAt; split <;> simp

theorem linkReply_replyViews_eq {st st' : SystemState} {rid : ReplyId} {c : ThreadId}
    (hInv : st.objects.invExt) (h : linkReply rid c st = .ok ((), st')) :
    st'.replyViews = st.replyViews := by
  unfold linkReply at h
  split at h
  · split at h
    · exact replyViews_storeReply_eq hInv (by assumption) h
    · cases h
  · cases h

theorem consumeReply_replyViews_eq {st st' : SystemState} {rid : ReplyId}
    (hInv : st.objects.invExt) (h : consumeReply rid st = .ok ((), st')) :
    st'.replyViews = st.replyViews := by
  unfold consumeReply at h
  split at h
  · exact replyViews_storeReply_eq hInv (by assumption) h
  · cases h; rfl

theorem linkCallerReply_replyViews_eq {st st' : SystemState} {c : ThreadId} {rid : ReplyId}
    (hInv : st.objects.invExt) (h : linkCallerReply c rid st = .ok ((), st')) :
    st'.replyViews = st.replyViews := by
  unfold linkCallerReply at h
  split at h
  · cases h
  · rename_i st1 h1
    have hI1 := linkReply_preserves_objects_invExt _ _ _ _ hInv h1
    split at h
    · cases h
    · split at h
      · rename_i tcb hT _
        exact (replyViews_storeTcb_eq hI1 hT h rfl).trans (linkReply_replyViews_eq hInv h1)
      · cases h

theorem linkCallerReply_objects_invExt {st st' : SystemState} {c : ThreadId} {rid : ReplyId}
    (hInv : st.objects.invExt) (h : linkCallerReply c rid st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold linkCallerReply at h
  split at h
  · cases h
  · rename_i st1 h1
    have hI1 := linkReply_preserves_objects_invExt _ _ _ _ hInv h1
    split at h
    · cases h
    · split at h
      · exact storeObject_preserves_objects_invExt _ _ _ _ hI1 h
      · cases h

theorem linkServerStashedReply_replyViews_eq {st st' : SystemState} {c s : ThreadId}
    (hInv : st.objects.invExt) (h : linkServerStashedReply c s st = .ok ((), st')) :
    st'.replyViews = st.replyViews := by
  unfold linkServerStashedReply at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i st1 h1
      have hI1 := linkCallerReply_objects_invExt hInv h1
      have hV1 := linkCallerReply_replyViews_eq hInv h1
      split at h
      · cases h; exact hV1
      · rename_i tcb hT
        exact (replyViews_storeTcb_eq hI1 hT h rfl).trans hV1

theorem consumeCallerReply_replyViews_eq {st st' : SystemState} {c : ThreadId} {rid : ReplyId}
    (hInv : st.objects.invExt) (h : consumeCallerReply c rid st = .ok ((), st')) :
    st'.replyViews = st.replyViews := by
  unfold consumeCallerReply at h
  split at h
  · cases h
  · rename_i st1 h1
    have hI1 := consumeReply_preserves_objects_invExt _ _ _ hInv h1
    have hV1 := consumeReply_replyViews_eq hInv h1
    split at h
    · cases h; exact hV1
    · rename_i tcb hT
      exact (replyViews_storeTcb_eq hI1 hT h rfl).trans hV1

theorem spliceReplyFrameStores_replyViews_eq {st st' : SystemState} {rid above : ReplyId}
    {r a : Reply} (hInv : st.objects.invExt) (hR : st.getReply? rid = some r)
    (hA : st.getReply? above = some a) (h : spliceReplyFrameStores st rid above r a = .ok st') :
    st'.replyViews = st.replyViews := by
  rcases spliceReplyFrameStores_cases h with ⟨_, hS⟩ | ⟨_, _, s1, s2, hB, hS1, hS2, hS3⟩
  · exact replyViews_storeReply_eq hInv hA hS
  · have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
    have hI2 := storeObject_preserves_objects_invExt _ _ _ _ hI1 hS2
    have hV1 := replyViews_storeReply_eq hInv hA hS1
    have hV2 : s2.replyViews = st.replyViews :=
      (replyViews_storeObject_eq hI1 hS2
        (by rw [hV1]; exact replyViews_of_getReply (spliceFrameBelow?_eq_some hB).2.2.1) rfl).trans hV1
    exact (replyViews_storeObject_eq hI2 hS3 (by rw [hV2]; exact replyViews_of_getReply hR) rfl).trans
      hV2

theorem spliceReplyFrameOut_replyViews_eq {st st' : SystemState} {rid : ReplyId}
    (hInv : st.objects.invExt) (h : spliceReplyFrameOut st rid = .ok st') :
    st'.replyViews = st.replyViews := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨_, _, _, hR, _, hA, _, hS⟩
  · rfl
  · exact spliceReplyFrameStores_replyViews_eq hInv hR hA hS

theorem spliceReplyFrameOutOrSelf_replyViews_eq (st : SystemState) (rid : ReplyId)
    (hInv : st.objects.invExt) : (spliceReplyFrameOutOrSelf st rid).replyViews = st.replyViews := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]
  · exact spliceReplyFrameOut_replyViews_eq hInv h

theorem removeCallerReplyFrame_replyViews_eq {st st' : SystemState} {c : ThreadId} {rid : ReplyId}
    (hInv : st.objects.invExt) (h : removeCallerReplyFrame c rid st = .ok ((), st')) :
    st'.replyViews = st.replyViews :=
  (consumeCallerReply_replyViews_eq (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hInv)
    h).trans (spliceReplyFrameOutOrSelf_replyViews_eq st rid hInv)

theorem replyViews_of_endpoint {st : SystemState} {k : ObjId} {ep : Endpoint}
    (h : st.objects[k]? = some (.endpoint ep)) : st.replyViews k = none := by
  unfold replyViews getObject?; rw [h]; rfl

/-- **The endpoint-queue pop keeps the views**: an endpoint store and two
queue-link writes. -/
theorem endpointQueuePopHead_replyViews_eq {eid : ObjId} {isRecv : Bool} {st st' : SystemState}
    {tid : ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (hStep : endpointQueuePopHead eid isRecv st = .ok (tid, tcb, st')) :
    st'.replyViews = st.replyViews := by
  unfold endpointQueuePopHead SystemState.getObject? at hStep
  cases hObj : st.objects[eid]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isRecv then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some htcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep
          revert hStep
          cases hStore : storeObject eid _ st with
          | error e => simp
          | ok pair =>
            obtain ⟨u, st1⟩ := pair; cases u
            have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hStore
            have hV1 := replyViews_storeObject_eq hInv hStore (replyViews_of_endpoint hObj) rfl
            cases hNext : htcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks st1 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact (replyViews_storeTcbQueueLinks hI1 hFinal).trans hV1
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb st1 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks st1 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hI2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hI1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact ((replyViews_storeTcbQueueLinks hI2 hFinal).trans
                      (replyViews_storeTcbQueueLinks hI1 hLink)).trans hV1

/-- **The endpoint-queue append keeps the views.** -/
theorem endpointQueueEnqueue_replyViews_eq {eid : ObjId} {isRecv : Bool} {tid : ThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : endpointQueueEnqueue eid isRecv tid st = .ok st') : st'.replyViews = st.replyViews := by
  unfold endpointQueueEnqueue SystemState.getObject? at h
  cases hObj : st.objects[eid]? with
  | none => simp [hObj] at h
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hObj] at h
    | endpoint ep =>
      simp only [hObj] at h
      have hE := replyViews_of_endpoint hObj
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
          cases hS : storeObject eid _ st with
          | error e => simp
          | ok pair =>
            obtain ⟨u, st1⟩ := pair; cases u
            intro h
            exact (replyViews_storeTcbQueueLinks
              (storeObject_preserves_objects_invExt _ _ _ _ hInv hS) h).trans
              (replyViews_storeObject_eq hInv hS hE rfl)
        | some tailTid =>
          simp only []
          cases hLT : lookupTcb st tailTid with
          | none => simp
          | some tailTcb =>
            simp only []
            cases hS : storeObject eid _ st with
            | error e => simp
            | ok pair =>
              obtain ⟨u, st1⟩ := pair; cases u
              simp only []
              have hI1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
              cases h2 : storeTcbQueueLinks st1 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
              | error e => simp
              | ok st2 =>
                simp only []
                intro h
                exact ((replyViews_storeTcbQueueLinks
                  (storeTcbQueueLinks_preserves_objects_invExt _ _ _ _ _ _ hI1 h2) h).trans
                  (replyViews_storeTcbQueueLinks hI1 h2)).trans (replyViews_storeObject_eq hInv hS hE rfl)

/-- **A step that maps each TCB to one with the same view, and creates no TCB,
keeps the views.** -/
theorem replyViews_eq_of_tcbs {st st' : SystemState}
    (hFwd : ∀ (k : ObjId) (t0 : TCB), st.objects[k]? = some (.tcb t0) →
      ∃ t' : TCB, st'.objects[k]? = some (.tcb t') ∧ t'.replyView = t0.replyView)
    (hBwd : ∀ (k : ObjId) (t' : TCB), st'.objects[k]? = some (.tcb t') →
      ∃ t0 : TCB, st.objects[k]? = some (.tcb t0)) :
    st'.replyViews = st.replyViews := by
  funext k
  cases h0 : st.objects[k]? with
  | some o =>
    cases o with
    | tcb t0 =>
      obtain ⟨t', h', hv⟩ := hFwd k t0 h0
      rw [replyViews_of_tcb h', replyViews_of_tcb h0, hv]
    | _ =>
      unfold replyViews getObject?
      rw [h0]
      cases h' : st'.objects[k]? with
      | none => rfl
      | some o' =>
        cases o' with
        | tcb t' => obtain ⟨_, h⟩ := hBwd k t' h'; rw [h0] at h; cases h
        | _ => rfl
  | none =>
    unfold replyViews getObject?
    rw [h0]
    cases h' : st'.objects[k]? with
    | none => rfl
    | some o' =>
      cases o' with
      | tcb t' => obtain ⟨_, h⟩ := hBwd k t' h'; rw [h0] at h; cases h
      | _ => rfl

theorem replyView_of_tcbBindingRewrite {a b : TCB} (h : tcbBindingRewrite a b) :
    a.replyView = b.replyView := by
  obtain ⟨_, rfl⟩ := h; rfl

/-- **The donation return rewrites scheduling-context bindings alone.** -/
theorem returnDonatedSchedContext_replyViews_eq {st st' : SystemState} {s : ThreadId}
    {scId : SchedContextId} {owner : ThreadId} {newOwner? : Option ThreadId}
    (hInv : st.objects.invExt) (h : returnDonatedSchedContext st s scId owner newOwner? = .ok st') :
    st'.replyViews = st.replyViews :=
  replyViews_eq_of_tcbs
    (fun k t0 hk => by
      obtain ⟨t', h', hR⟩ := returnDonatedSchedContext_tcb_rewrite _ _ _ _ _ hInv _ h k t0 hk
      exact ⟨t', h', replyView_of_tcbBindingRewrite hR⟩)
    (fun k t' hk => by
      obtain ⟨t0, h0, -⟩ := returnDonatedSchedContext_tcb_rewrite_backward _ _ _ _ _ _ hInv h k t' hk
      exact ⟨t0, h0⟩)

theorem returnDonatedSchedContextResolved_replyViews_eq {st st' : SystemState} {s : ThreadId}
    {scId : SchedContextId} {owner : ThreadId} (hInv : st.objects.invExt)
    (h : returnDonatedSchedContextResolved st s scId owner = .ok st') :
    st'.replyViews = st.replyViews :=
  returnDonatedSchedContextResolved_lift (P := fun x => x.replyViews = st.replyViews) h
    (fun _ _ hPop => returnDonatedSchedContext_replyViews_eq hInv hPop)

theorem cleanupPreReceiveDonationChecked_replyViews_eq {st st' : SystemState} {r : ThreadId}
    (hInv : st.objects.invExt) (h : cleanupPreReceiveDonationChecked st r = .ok st') :
    st'.replyViews = st.replyViews := by
  unfold cleanupPreReceiveDonationChecked at h
  split at h
  · cases h; rfl
  · split at h
    · exact returnDonatedSchedContextResolved_replyViews_eq hInv h
    · cases h; rfl

theorem replyViews_storeTcbIpcStateAndMessage_fromTcb {st st' : SystemState} {t : ThreadId}
    {tcb : TCB} {s : ThreadIpcState} {m : Option IpcMessage} (hInv : st.objects.invExt)
    (hOld : st.objects[t.toObjId]? = some (.tcb tcb))
    (h : storeTcbIpcStateAndMessage_fromTcb st t tcb s m = .ok st') :
    st'.replyViews = ReplyViews.setServer st.replyViews t (ipcServer? s) := by
  unfold storeTcbIpcStateAndMessage_fromTcb at h
  split at h
  · cases h
  · rename_i st1 hS
    cases h
    exact replyViews_storeObject_tcb hInv hS hOld (by
      simp only [TCB.replyView, blockingServer?_eq_ipcServer?, TCB.ipcState_setIpcState])

theorem storeTcbIpcStateAndMessage_fromTcb_objects_invExt {st st' : SystemState} {t : ThreadId}
    {tcb : TCB} {s : ThreadIpcState} {m : Option IpcMessage} (hInv : st.objects.invExt)
    (h : storeTcbIpcStateAndMessage_fromTcb st t tcb s m = .ok st') : st'.objects.invExt := by
  unfold storeTcbIpcStateAndMessage_fromTcb at h
  split at h
  · cases h
  · rename_i st1 hS; cases h; exact storeObject_preserves_objects_invExt _ _ _ _ hInv hS

/-- **The endpoint-queue removal writes queue links alone.** -/
theorem endpointQueueRemove_replyViews_eq {eid : ObjId} {isRecv : Bool} {tid : ThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : endpointQueueRemove eid isRecv tid st = .ok st') : st'.replyViews = st.replyViews :=
  replyViews_eq_of_tcbs
    (fun k t0 hk => by
      rw [RHTable_getElem?_eq_get?] at hk
      obtain ⟨t', h', hv⟩ := endpointQueueRemove_getTcb_upToField TCB.replyView
        (fun _ _ _ _ => rfl) _ _ _ _ _ hInv h k t0 hk
      rw [← RHTable_getElem?_eq_get?] at h'
      exact ⟨t', h', hv.symm⟩)
    (fun k t' hk => by
      obtain ⟨t0, h0, -⟩ := endpointQueueRemove_getTcb_backward_upToField TCB.replyView
        (fun _ _ _ _ => rfl) _ _ _ _ _ hInv h k t' hk
      exact ⟨t0, h0⟩)

end SeLe4n.Model.SystemState
