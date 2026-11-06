-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Tails

/-!
# The IPC primitives' record frames

WS-ZA ZA6.37.  The writes the IPC arms are built from, each as the frame it
keeps: the endpoint-queue links and the stored endpoints keep every record view
(`RecordsFrame`); a write to a thread's IPC state keeps the address-space
records and leaves every fault record parked (`RecordsStep`) when the thread
was not fault-blocked or is fault-blocked after it (`TcbStaysParked`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  One thread's write
-- ============================================================================

/-- **A thread write that keeps its fault record parked**: the thread after the
write carries a fault only parked, given the thread before it did. -/
def TcbStaysParked (x y : TCB) : Prop :=
  y.pendingFault.isSome → (x.pendingFault.isSome → x.faultParked) → y.faultParked

namespace TcbStaysParked

theorem of_view {x y : TCB} (h : y.recordView = x.recordView) : TcbStaysParked x y := by
  intro hF H
  simp only [TCB.recordView, TcbRecordView.mk.injEq] at h
  obtain ⟨-, hi, hs, hf⟩ := h
  have := H (hf ▸ hF)
  unfold TCB.faultParked at this ⊢
  rw [hi, hs]; exact this

/-- An IPC-state write keeping the fault record and the thread state, out of an
unparked state or into a parked one. -/
theorem of_ipc {x y : TCB} (hpf : y.pendingFault = x.pendingFault)
    (hts : y.threadState = x.threadState) (h : ¬ ipcParked x.ipcState ∨ ipcParked y.ipcState) :
    TcbStaysParked x y := by
  intro hF H
  rcases H (hpf ▸ hF) with hI | hP
  · exact .inl (hts.trans hI)
  · rcases h with hN | hP'
    · exact absurd hP hN
    · exact .inr hP'

/-- A write that leaves the thread carrying no fault. -/
theorem of_noFault {x y : TCB} (h : y.pendingFault = none) : TcbStaysParked x y := by
  intro hF; rw [h] at hF; cases hF

/-- A write into a parked state. -/
theorem of_parked {x y : TCB} (h : y.faultParked) : TcbStaysParked x y := fun _ _ => h

end TcbStaysParked

namespace RecordsStep

/-- **A TCB stored over a TCB.** -/
theorem storeObject_tcb {st st' : SystemState} {t : SeLe4n.ThreadId} {x y : TCB}
    (hInv : st.objects.invExt) (hOld : st.objects[t.toObjId]? = some (.tcb x))
    (h : storeObject t.toObjId (.tcb y) st = .ok ((), st')) (hS : TcbStaysParked x y) :
    RecordsStep st st' := by
  refine ⟨fun k => ?_, ?_, storeObject_preserves_objects_invExt st st' _ _ hInv h, ?_,
    by rw [storeObject_machine_eq st st' _ _ h]⟩
  · by_cases hk : k = t.toObjId
    · subst hk; rw [storeObject_objects_eq st st' _ _ hInv h, hOld]; rfl
    · rw [storeObject_objects_ne st st' _ k _ hk hInv h]
  · rw [storeObject_asidTable_non_vspaceRoot st st' _ _ (fun _ => by simp) h, hOld]
  · intro u tcb' hT hF H
    have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    by_cases hk : u.toObjId = t.toObjId
    · rw [hk, storeObject_objects_eq st st' _ _ hInv h] at hO
      cases hO
      exact hS hF (H x ((SystemState.getTcb?_eq_some_iff _ _ _).mpr (hk ▸ hOld)))
    · rw [storeObject_objects_ne st st' _ _ _ hk hInv h] at hO
      exact H tcb' ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO) hF

/-- **The checked TCB write**, when it keeps the thread's fault record parked. -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st')
    (hS : ∀ x, st.getTcb? t = some x → TcbStaysParked x (f x)) : RecordsStep st st' := by
  obtain ⟨tcb, hL, hSt⟩ := modifyTcb_ok_decompose h
  have hT := lookupTcb_some_objects st t tcb hL
  exact storeObject_tcb hInv hT hSt (hS tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hT))

/-- **The unchecked TCB write**, likewise. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hS : ∀ x, st.getTcb? t = some x → TcbStaysParked x (f x)) :
    RecordsStep st (st.updateTcb t f) := by
  have hF : FaultsStayParked st (st.updateTcb t f) := by
    intro u tcb' hU hF H
    by_cases hk : t.toObjId = u.toObjId
    · have hu : u = t := (SeLe4n.ThreadId.toObjId_injective _ _ hk).symm
      subst hu
      rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv] at hU
      cases hT : st.getTcb? u with
      | none => rw [hT] at hU; cases hU
      | some x =>
        rw [hT] at hU; cases hU
        exact hS x hT hF (H x hT)
    · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInv _ hk] at hU
      exact H tcb' hU hF
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact refl hInv
  | some x =>
    have hInv' := SystemState.updateTcb_preserves_objects_invExt st t f hInv
    rw [SystemState.updateTcb_eq_of_some hT] at hF hInv' ⊢
    have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    refine ⟨fun k => ?_, rfl, hInv', hF, rfl⟩
    show rootViewOf (st.objects.insert t.toObjId _)[k]? = _
    simp only [RHTable_getElem?_eq_get?] at hO ⊢
    by_cases hx : t.toObjId = k
    · subst hx; rw [RobinHood.RHTable.getElem?_insert_self _ _ _ hInv, hO]; rfl
    · rw [RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb)) hInv]

end RecordsStep

-- ============================================================================
-- §2  The endpoint-queue links
-- ============================================================================

namespace RecordsFrame

/-- An endpoint stored over an endpoint. -/
theorem storeEndpoint {st st' : SystemState} {eid : SeLe4n.ObjId} {ep ep' : Endpoint}
    (hInv : st.objects.invExt) (hObj : st.objects[eid]? = some (.endpoint ep))
    (h : SeLe4n.Model.storeObject eid (.endpoint ep') st = .ok ((), st')) : RecordsFrame st st' :=
  storeObject hInv h (by rw [hObj]; rfl) (fun _ h => by cases h)

/-- A notification stored over a notification. -/
theorem storeNotification {st st' : SystemState} {nid : SeLe4n.ObjId} {n n' : Notification}
    (hInv : st.objects.invExt) (hObj : st.objects[nid]? = some (.notification n))
    (h : SeLe4n.Model.storeObject nid (.notification n') st = .ok ((), st')) : RecordsFrame st st' :=
  storeObject hInv h (by rw [hObj]; rfl) (fun _ h => by cases h)

/-- A reply stored over a reply. -/
theorem storeReply {st st' : SystemState} {rid : SeLe4n.ObjId} {r r' : Reply}
    (hInv : st.objects.invExt) (hObj : st.objects[rid]? = some (.reply r))
    (h : SeLe4n.Model.storeObject rid (.reply r') st = .ok ((), st')) : RecordsFrame st st' :=
  storeObject hInv h (by rw [hObj]; rfl) (fun _ h => by cases h)

/-- A scheduling context stored over a scheduling context. -/
theorem storeSchedContext {st st' : SystemState} {k : SeLe4n.ObjId} {s s' : SchedContext}
    (hInv : st.objects.invExt) (hObj : st.objects[k]? = some (.schedContext s))
    (h : SeLe4n.Model.storeObject k (.schedContext s') st = .ok ((), st')) : RecordsFrame st st' :=
  storeObject hInv h (by rw [hObj]; rfl) (fun _ h => by cases h)

theorem storeTcbQueueLinks {st st' : SystemState} {t : SeLe4n.ThreadId}
    {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev} {next : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeTcbQueueLinks st t prev pprev next = .ok st') :
    RecordsFrame st st' :=
  modifyTcb (f := fun tcb => tcbWithQueueLinks tcb prev pprev next) hInv (fun _ => rfl) h

/-- **The endpoint-queue pop keeps every record view**: an endpoint store and two
queue-link writes. -/
theorem endpointQueuePopHead {eid : SeLe4n.ObjId} {isRecv : Bool} {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.endpointQueuePopHead eid isRecv st = .ok (tid, tcb, st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.endpointQueuePopHead SystemState.getObject? at hStep
  cases hObj : st.objects[eid]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _
    | frame _ | pageTable _ => simp [hObj] at hStep
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
          revert hStep
          cases hStore : SeLe4n.Model.storeObject eid _ st with
          | error e => simp
          | ok pair =>
            obtain ⟨u, st1⟩ := pair; cases u
            have F1 := storeEndpoint hInv hObj hStore
            cases hNext : htcb.queueNext with
            | none =>
              simp only []
              cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks st1 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact F1.trans (storeTcbQueueLinks F1.invExt hFinal)
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
                  have F2 := F1.trans (storeTcbQueueLinks F1.invExt hLink)
                  cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact F2.trans (storeTcbQueueLinks F2.invExt hFinal)

/-- **The endpoint-queue append keeps every record view.** -/
theorem endpointQueueEnqueue {eid : SeLe4n.ObjId} {isRecv : Bool} {tid : SeLe4n.ThreadId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.endpointQueueEnqueue eid isRecv tid st = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.endpointQueueEnqueue SystemState.getObject? at h
  cases hObj : st.objects[eid]? with
  | none => simp [hObj] at h
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _
    | frame _ | pageTable _ => simp [hObj] at h
    | endpoint ep =>
      simp only [hObj] at h
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
            have F1 := storeEndpoint hInv hObj hS
            exact F1.trans (storeTcbQueueLinks F1.invExt h)
        | some tailTid =>
          simp only []
          cases hLT : lookupTcb st tailTid with
          | none => simp
          | some tailTcb =>
            simp only []
            cases hS : SeLe4n.Model.storeObject eid _ st with
            | error e => simp
            | ok pair =>
              obtain ⟨u, st1⟩ := pair; cases u
              simp only []
              have F1 := storeEndpoint hInv hObj hS
              cases h2 : _root_.SeLe4n.Kernel.storeTcbQueueLinks st1 tailTid tailTcb.queuePrev
                  tailTcb.queuePPrev (some tid) with
              | error e => simp
              | ok st2 =>
                simp only []
                intro h
                have F2 := F1.trans (storeTcbQueueLinks F1.invExt h2)
                exact F2.trans (storeTcbQueueLinks F2.invExt h)

end RecordsFrame

-- ============================================================================
-- §3  In-place thread writes, the wake and the dequeue
-- ============================================================================

open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsStep

/-- **A thread rewritten in its slot**, keeping its fault record parked. -/
theorem mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) {g : TCB → TCB}
    (hInv : st.objects.invExt) (hS : ∀ x, st.getTcb? t = some x → TcbStaysParked x (g x)) :
    RecordsStep st (st.mapTcbInPlace t g) := by
  refine ⟨fun k => ?_, rfl, SystemState.mapTcbInPlace_objects_invExt _ _ _ hInv, ?_, rfl⟩
  · rw [SystemState.objects_mapTcbInPlace]
    split
    · cases st.objects[k]? with
      | none => rfl
      | some o => cases o <;> rfl
    · rfl
  · intro u tcb' hU hF H
    by_cases hk : t.toObjId = u.toObjId
    · have hu : u = t := (SeLe4n.ThreadId.toObjId_injective _ _ hk).symm
      subst hu
      rw [SystemState.mapTcbInPlace_getTcb?_self] at hU
      cases hT : st.getTcb? u with
      | none => rw [hT] at hU; cases hU
      | some x => rw [hT] at hU; cases hU; exact hS x hT hF (H x hT)
    · rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hk] at hU
      exact H tcb' hU hF

end RecordsStep

namespace RecordsFrame

/-- A thread rewritten in its slot with its record view kept. -/
theorem mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) {g : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (g x).recordView = x.recordView) :
    RecordsFrame st (st.mapTcbInPlace t g) := by
  refine ⟨fun k => ?_, rfl, SystemState.mapTcbInPlace_objects_invExt _ _ _ hInv, rfl⟩
  rw [SystemState.objects_mapTcbInPlace]
  split
  · cases st.objects[k]? with
    | none => rfl
    | some o => cases o <;> simp [KernelObject.mapTcb, recordViewOf, hf]
  · rfl

/-- Setting the IPC state a thread already holds keeps its record view. -/
theorem setIpcState_recordView_of_eq {x : TCB} {s : ThreadIpcState} (h : x.ipcState = s) :
    (x.setIpcState s).recordView = x.recordView := by
  subst h; rw [TCB.setIpcState_ipcState]

/-- **The wake of a thread already `.ready`** keeps every record view: its
`.ready` mark rewrites nothing, and the enqueue writes run links. -/
theorem enqueueRunnableOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hR : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready) :
    RecordsFrame st (_root_.SeLe4n.Kernel.enqueueRunnableOnCore st c tid) := by
  unfold _root_.SeLe4n.Kernel.enqueueRunnableOnCore
  split
  · rename_i tcb hT _
    split
    · exact refl hInv
    · dsimp only
      have hO := (SystemState.getTcb?_eq_some_iff st tid tcb).1 hT
      have F1 := rewriteObject (k := tid.toObjId) (o := .tcb (tcb.setIpcState .ready))
        (SystemState.rewriteAdmissible_tcb ‹_› _) hInv
        (by rw [hO]; simp [setIpcState_recordView_of_eq (hR tcb hT)])
      have F2 := F1.trans (of_runLinkStep
        (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ c tid tcb.boostedPriority)
        (SystemState.runEnqueueAdmitted_replyViews_eq _ _ _ _)
        (SystemState.runEnqueueAdmitted_onlyObjectsSchedulerDiffer _ _ _ _)
        (SystemState.runEnqueueAdmitted_objects_invExt _ _ _ _ F1.invExt))
      exact F2.trans (withScheduler _ _ F2.invExt)
  · exact refl hInv

theorem wakeThread (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) (hR : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready) :
    RecordsFrame st (_root_.SeLe4n.Kernel.wakeThread st tid c).1 :=
  enqueueRunnableOnCore st _ tid hInv hR

theorem runDescheduleOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (st.runDescheduleOnCore c t) :=
  of_runLinkStep (SystemState.runDescheduleOnCore_objectsAgreeOffRunLinks st c t)
    (by
      have := SystemState.runRemoveOnCore_replyViews_eq st c t
      exact this)
    (SystemState.runDescheduleOnCore_onlyObjectsSchedulerDiffer st c t)
    (SystemState.runDescheduleOnCore_objects_invExt st c t hInv)

theorem removeRunnableOnCore (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.removeRunnableOnCore st t c) :=
  runDescheduleOnCore st c t hInv

theorem recordSendCap (st : SystemState) (t : SeLe4n.ThreadId) (b : Option SeLe4n.Badge)
    (g : Bool) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.recordSendCap st t b g) :=
  mapTcbInPlace st t hInv fun _ => rfl

end RecordsFrame

namespace RecordsStep

/-- An IPC-state and message store, out of an unparked state or into a parked
one. -/
theorem storeTcbIpcStateAndMessage {st st' : SystemState} {t : SeLe4n.ThreadId}
    {s : ThreadIpcState} {m : Option IpcMessage} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbIpcStateAndMessage st t s m = .ok st')
    (hP : ∀ x, st.getTcb? t = some x → ¬ ipcParked x.ipcState ∨ ipcParked s) :
    RecordsStep st st' :=
  modifyTcb hInv h fun x hx => TcbStaysParked.of_ipc rfl rfl (by simpa using hP x hx)

theorem storeTcbIpcState {st st' : SystemState} {t : SeLe4n.ThreadId} {s : ThreadIpcState}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeTcbIpcState st t s = .ok st')
    (hP : ∀ x, st.getTcb? t = some x → ¬ ipcParked x.ipcState ∨ ipcParked s) :
    RecordsStep st st' :=
  modifyTcb hInv h fun x hx => TcbStaysParked.of_ipc rfl rfl (by simpa using hP x hx)

/-- The receive completion: the woken thread made `.ready` out of an unparked
state. -/
theorem storeTcbReceiveComplete {st st' : SystemState} {t : SeLe4n.ThreadId}
    {m : Option IpcMessage} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbReceiveComplete st t m = .ok st')
    (hP : ∀ x, st.getTcb? t = some x → ¬ ipcParked x.ipcState) : RecordsStep st st' :=
  modifyTcb hInv h fun x hx => TcbStaysParked.of_ipc rfl rfl (by simpa using hP x hx)

end RecordsStep

-- ============================================================================
-- §4  The reply links and the reply-waiter links
-- ============================================================================

/-- A checked TCB write leaves every other thread as it was. -/
theorem modifyTcb_getTcb?_ne {st st' : SystemState} {t u : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st')
    (hne : t.toObjId ≠ u.toObjId) : st'.getTcb? u = st.getTcb? u := by
  obtain ⟨tcb, -, hS⟩ := modifyTcb_ok_decompose h
  unfold SystemState.getTcb?
  rw [storeObject_objects_ne st st' _ _ _ (Ne.symm hne) hInv hS]

theorem TcbStaysParked.of_fields {x y : TCB} (hpf : y.pendingFault = x.pendingFault)
    (hts : y.threadState = x.threadState) (hi : y.ipcState = x.ipcState) : TcbStaysParked x y := by
  intro hF H
  have := H (hpf ▸ hF)
  unfold TCB.faultParked at this ⊢
  rw [hts, hi]; exact this

namespace RecordsStep

theorem updateTcbAtCode (st : SystemState) (k : Nat) {g : TCB → TCB} (hInv : st.objects.invExt)
    (hS : ∀ x, TcbStaysParked x (g x)) : RecordsStep st (st.updateTcbAtCode k g) := by
  unfold SystemState.updateTcbAtCode
  split
  · exact refl hInv
  · exact mapTcbInPlace st _ hInv fun x _ => hS x

/-- An in-place thread write keeping its fault record, thread state and IPC
state. -/
theorem mapTcbInPlace_fields (st : SystemState) (t : SeLe4n.ThreadId) {g : TCB → TCB}
    (hInv : st.objects.invExt)
    (hf : ∀ x, (g x).pendingFault = x.pendingFault ∧ (g x).threadState = x.threadState ∧
      (g x).ipcState = x.ipcState := by intro _; exact ⟨rfl, rfl, rfl⟩) :
    RecordsStep st (st.mapTcbInPlace t g) :=
  mapTcbInPlace st t hInv fun x _ => TcbStaysParked.of_fields (hf x).1 (hf x).2.1 (hf x).2.2

theorem updateTcbAtCode_fields (st : SystemState) (k : Nat) {g : TCB → TCB}
    (hInv : st.objects.invExt)
    (hf : ∀ x, (g x).pendingFault = x.pendingFault ∧ (g x).threadState = x.threadState ∧
      (g x).ipcState = x.ipcState := by intro _; exact ⟨rfl, rfl, rfl⟩) :
    RecordsStep st (st.updateTcbAtCode k g) :=
  updateTcbAtCode st k hInv fun x => TcbStaysParked.of_fields (hf x).1 (hf x).2.1 (hf x).2.2

/-- **The reply-waiter link writes keep every thread's fault record and state.** -/
theorem linkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsStep st (st.linkReplyWaiter w s) := by
  unfold SystemState.linkReplyWaiter
  dsimp only
  have S1 := mapTcbInPlace_fields st w hInv (g := fun x => { x with
    replyWaiterPrevCode := 0, replyWaiterNextCode := st.replyHeadCode s })
  have S2 := S1.trans (updateTcbAtCode_fields _ (st.replyHeadCode s) S1.invExt
    (g := fun x => { x with replyWaiterPrevCode := SeLe4n.Kernel.LinkedQueue.code w }))
  exact S2.trans (mapTcbInPlace_fields _ s S2.invExt)

theorem unlinkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsStep st (st.unlinkReplyWaiter w s) := by
  unfold SystemState.unlinkReplyWaiter
  dsimp only
  have S1 := updateTcbAtCode_fields st (st.replyPrevCode w) hInv
    (g := fun x => { x with replyWaiterNextCode := st.replyNextCode w })
  have S2 := S1.trans (updateTcbAtCode_fields _ (st.replyNextCode w) S1.invExt
    (g := fun x => { x with replyWaiterPrevCode := st.replyPrevCode w }))
  have S3 := S2.trans (mapTcbInPlace_fields _ s S2.invExt (g := fun x => { x with
    replyWaitersHeadCode := if st.replyPrevCode w = 0 then st.replyNextCode w
      else x.replyWaitersHeadCode,
    replyWaitersCount := x.replyWaitersCount - 1 }))
  exact S3.trans (mapTcbInPlace_fields _ w S3.invExt)

theorem unlinkReplyWaiterOpt (st : SystemState) (w : SeLe4n.ThreadId) (s? : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsStep st (st.unlinkReplyWaiterOpt w s?) := by
  cases s? with
  | none => exact refl hInv
  | some s => exact unlinkReplyWaiter st w s hInv

end RecordsStep

namespace RecordsFrame

theorem linkReply {rid : SeLe4n.ReplyId} {caller : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : SystemState.linkReply rid caller st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold SystemState.linkReply at h
  cases hR : st.getReply? rid with
  | none => simp [hR] at h
  | some r =>
    simp only [hR] at h
    split at h
    · exact storeReply hInv ((SystemState.getReply?_eq_some_iff st rid r).mp hR) h
    · simp at h

theorem linkCallerReply {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold SystemState.linkCallerReply at h
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at h
  | ok p1 =>
    obtain ⟨⟨⟩, st1⟩ := p1
    simp only [hLink] at h
    have F1 := linkReply hInv hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at h
    | some tcb =>
      simp only [hT] at h
      split at h
      · exact F1.trans (storeObject F1.invExt h
          (by rw [(SystemState.getTcb?_eq_some_iff st1 caller tcb).mp hT]; rfl)
          (fun _ h => by cases h))
      · simp at h

theorem recordReplyStasher (st : SystemState) (code : Nat) (recv : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (st.recordReplyStasher code recv) := by
  rcases SystemState.recordReplyStasher_eq_or st code recv with h | ⟨_, _, _, hR, hS⟩
  · rw [h]; exact refl hInv
  · exact storeReply hInv hR hS

end RecordsFrame

end SeLe4n.Kernel
