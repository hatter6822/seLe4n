/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv
import SeLe4n.Kernel.RobinHood.Invariant.MapValueAtFold

/-!
# Reply-receive in place

WS-ZA ZA4.7.  A reply-receive that answers a caller blocked on the server and
then blocks the server on an endpoint no sender waits on is the reply's
in-place writes followed by the receive's (`replyRecvOnCore_blocks_inPlace`):
every check the receive leg makes is read on the pre-state and carried across
the reply leg (`storeReplyRendezvous_receiveGuard`), including the whole-table
scan for a stashed reply (`replyIsStashed_of_stashView`), which reads one code
per object that no write of the reply leg moves.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- What `replyIsStashed` reads of an object: the stashed reply object's code
of a thread blocked receiving, `0` for anything else. -/
def stashCode : KernelObject → Nat
  | .tcb t =>
      match t.ipcState with
      | .blockedOnReceive _ => t.pendingReceiveReplyCode
      | _ => 0
  | _ => 0

/-- `replyIsStashed`'s test of a thread is a test of its `stashCode`. -/
theorem stashTest_eq_stashCode (t : TCB) (rid : SeLe4n.ReplyId) :
    (match t.ipcState with
      | .blockedOnReceive _ => t.pendingReceiveReply == some rid
      | _ => false) = (stashCode (.tcb t) == rid.val + 1) := by
  cases h : t.ipcState <;> simp only [stashCode, h] <;> try simp
  rcases hc : t.pendingReceiveReplyCode with _ | k
  · simp [TCB.pendingReceiveReply, hc, SeLe4n.ReplyId.ofOptCode]
  · rcases rid with ⟨r⟩
    by_cases hkr : k = r
    · subst hkr; simp [TCB.pendingReceiveReply, hc, SeLe4n.ReplyId.ofOptCode]
    · have : ¬ (k + 1 = r + 1) := by omega
      simp [TCB.pendingReceiveReply, hc, SeLe4n.ReplyId.ofOptCode]
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact ⟨fun e => by cases e; rfl, fun e => by subst e; rfl⟩

/-- `replyIsStashed` reads each object only through `stashCode`. -/
theorem replyIsStashed_eq_fold_stashCode (st : SystemState) (rid : SeLe4n.ReplyId) :
    st.replyIsStashed rid =
      st.objects.fold false (fun acc _ v => (fun a x => a || x == rid.val + 1) acc (stashCode v)) := by
  unfold SystemState.replyIsStashed
  congr
  funext acc _k obj
  cases obj with
  | tcb t => exact congrArg (acc || ·) (stashTest_eq_stashCode t rid)
  | _ => simp [stashCode]

/-- The object table's slots, each read through `stashCode`. -/
def stashView (st : SystemState) : List (Option Nat) := st.objects.slotView stashCode

/-- **`replyIsStashed` sees only the stash view.** -/
theorem replyIsStashed_of_stashView {st st' : SystemState} (h : stashView st' = stashView st)
    (rid : SeLe4n.ReplyId) : st'.replyIsStashed rid = st.replyIsStashed rid := by
  rw [replyIsStashed_eq_fold_stashCode, replyIsStashed_eq_fold_stashCode]
  exact RHTable.fold_eq_of_slotView st.objects st'.objects stashCode false
    (fun a x => a || x == rid.val + 1) h

theorem stashView_of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    stashView st' = stashView st := by
  unfold stashView; rw [h]

/-- A TCB rewritten in its slot keeps the stash view when the rewrite keeps
the stash of the TCB the thread holds. -/
theorem stashView_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (h : ∀ x, st.getTcb? t = some x → stashCode (.tcb (g x)) = stashCode (.tcb x)) :
    stashView (st.mapTcbInPlace t g) = stashView st := by
  unfold stashView SystemState.mapTcbInPlace
  apply RHTable.slotView_mapValueAt
  intro v hv
  cases v with
  | tcb x =>
    exact h x ((SystemState.getTcb?_eq_some_iff _ _ _).mpr
      (by simpa only [RHTable_getElem?_eq_get?] using hv))
  | _ => rfl

theorem stashView_updateTcbAtCode (st : SystemState) (k : Nat) (g : TCB → TCB)
    (h : ∀ x, stashCode (.tcb (g x)) = stashCode (.tcb x)) :
    stashView (st.updateTcbAtCode k g) = stashView st := by
  unfold SystemState.updateTcbAtCode
  split
  · rfl
  · exact stashView_mapTcbInPlace _ _ _ (fun x _ => h x)

theorem stashView_modifyObject (st : SystemState) (x : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hNo : st.objects.noResizeDue)
    (h : ∀ v, st.objects.get? x = some v → stashCode (F v) = stashCode v) :
    stashView (st.modifyObject x F) = stashView st := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  exact RHTable.slotView_mapValueAt _ _ _ _ h

theorem stashView_updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hNo : st.objects.noResizeDue)
    (h : ∀ x, st.getTcb? t = some x → stashCode (.tcb (g x)) = stashCode (.tcb x)) :
    stashView (st.updateTcb t g) = stashView st := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
  exact stashView_mapTcbInPlace _ _ _ h

theorem stashView_runAppendOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : stashView (st.runAppendOnCore c t p) = stashView st := by
  show stashView (st.runAppendLinks c t p) = _
  unfold SystemState.runAppendLinks
  dsimp only
  rw [stashView_updateTcbAtCode, stashView_updateTcbAtCode, stashView_mapTcbInPlace]
  all_goals intros; rfl

theorem stashView_runEnqueueAdmitted (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : stashView (st.runEnqueueAdmitted c t p) = stashView st := by
  unfold SystemState.runEnqueueAdmitted
  dsimp only
  split
  · rfl
  · exact stashView_runAppendOnCore st c t p

/-- A wake keeps the stash view when the woken thread stashes nothing. -/
theorem stashView_enqueueRunnableOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue)
    (h : ∀ x, st.getTcb? t = some x → stashCode (.tcb x) = 0) :
    stashView (enqueueRunnableOnCore st c t) = stashView st := by
  rw [enqueueRunnableOnCore_eq_impl]
  unfold enqueueRunnableOnCoreImpl
  split
  · next x hx =>
    dsimp only
    split
    · rfl
    · show stashView ((st.modifyObject _ _).runEnqueueAdmitted c t _) = _
      rw [stashView_runEnqueueAdmitted, stashView_modifyObject _ _ _ hNo]
      intro v hv
      cases v with
      | tcb y =>
        have hy : st.getTcb? t = some y := (SystemState.getTcb?_eq_some_iff _ _ _).mpr
          (by simpa only [RHTable_getElem?_eq_get?] using hv)
        rw [h y hy]
        simp [SystemState.mapTcbObject, stashCode]
      | _ => rfl
  · rfl

theorem stashView_unlinkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) :
    stashView (st.unlinkReplyWaiter w s) = stashView st := by
  unfold SystemState.unlinkReplyWaiter
  dsimp only
  rw [stashView_mapTcbInPlace, stashView_mapTcbInPlace, stashView_updateTcbAtCode,
    stashView_updateTcbAtCode]
  all_goals intros; rfl

/-- **The reply's writes keep the stash view**: the answered caller, blocked on
its reply, stashes nothing before or after, and every other write is a link or
a reply object. -/
theorem stashView_storeReplyRendezvousReady (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (ep : SeLe4n.ObjId) (s? : Option SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) (hT : st.getTcb? c = some ct)
    (hIpc : ct.ipcState = .blockedOnReply ep s?) :
    stashView (storeReplyRendezvousReady st c server rid) = stashView st := by
  unfold storeReplyRendezvousReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  rw [stashView_unlinkReplyWaiter, stashView_updateTcb _ _ _ hNo3,
    stashView_modifyObject _ _ _ hNo2,
    stashView_enqueueRunnableOnCore _ _ _ hNo1,
    stashView_updateTcb _ _ _ hNo]
  · intro x hx
    rw [hT] at hx; cases hx
    simp [stashCode, receiverReady, hIpc]
  · intro x hx
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_getTcb?_self,
      hT] at hx
    cases hx
    simp [stashCode, receiverReady]
  · intro v _; cases v <;> rfl
  · intros; rfl

/-- The delivery's write keeps the stash view. -/
theorem stashView_hold (st : SystemState) (r : SeLe4n.ThreadId) (msg : IpcMessage) :
    stashView (st.mapTcbInPlace r (holdMessage msg)) = stashView st := by
  rw [stashView_mapTcbInPlace]
  intros; rfl

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyFrame

theorem objects_updateTcb_ne (s : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hNo : s.objects.noResizeDue) (x : SeLe4n.ObjId) (hx : x ≠ t.toObjId) :
    (s.updateTcb t g).objects[x]? = s.objects[x]? := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.objects_mapTcbInPlace,
    if_neg (fun h => hx (beq_iff_eq.mp h).symm)]

theorem objects_modifyObject_ne (s : SystemState) (k : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hNo : s.objects.noResizeDue) (x : SeLe4n.ObjId) (hx : x ≠ k) :
    (s.modifyObject k F).objects[x]? = s.objects[x]? := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.get?_mapValueAt, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]

theorem objects_modifyObject_self (s : SystemState) (k : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hNo : s.objects.noResizeDue) :
    (s.modifyObject k F).objects[k]? = (s.objects[k]?).map F := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.get?_mapValueAt, if_pos (beq_self_eq_true _)]

/-- The reply's writes change only the index-free part of the state. -/
theorem storeReplyRendezvousReady_fields (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    (storeReplyRendezvousReady st c server rid).objectIndexSet = st.objectIndexSet ∧
      (storeReplyRendezvousReady st c server rid).lifecycle = st.lifecycle := by
  unfold storeReplyRendezvousReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hD := enqueueRunnableOnCore_onlyObjectsSchedulerDiffer (st.updateTcb c receiverReady)
    (determineTargetCore (st.updateTcb c receiverReady) c) c
  rw [SystemState.unlinkReplyWaiter_eq_impl, SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo3,
    SystemState.modifyObject_eq_mapValueAt _ _ _ hNo2]
  unfold SystemState.unlinkReplyWaiterImpl SystemState.mapTcbInPlace
  dsimp only
  rw [hD, SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
  exact ⟨rfl, rfl⟩

/-- **Off the answered caller and its reply object, the reply's writes touch
only links.** -/
theorem storeReplyRendezvousReady_agree (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (hNo : st.objects.noResizeDue)
    (hT : st.getTcb? c = some ct) (hFC : st.objects.findsInPlace c.toObjId = true)
    (x : SeLe4n.ObjId) (hxc : x ≠ c.toObjId) (hxr : x ≠ rid.toObjId) :
    ((storeReplyRendezvousReady st c server rid).objects[x]?).map KernelObject.withoutRunLinks =
      (st.objects[x]?).map KernelObject.withoutRunLinks := by
  unfold storeReplyRendezvousReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hT1 : (st.updateTcb c receiverReady).getTcb? c = some (receiverReady ct) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_getTcb?_self, hT]
    rfl
  have hF1 : (st.updateTcb c receiverReady).objects.findsInPlace c.toObjId = true := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact (SystemState.mapTcbInPlace_keepsFinds _ _ _ _).trans hFC
  rw [SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ c server x,
    objects_updateTcb_ne _ _ _ hNo3 x hxc, objects_modifyObject_ne _ _ _ hNo2 x hxr,
    enqueueRunnableOnCore_agree_of_findsInPlace _ _ c (receiverReady ct) hT1
      (by simp [receiverReady]) hF1 x,
    objects_updateTcb_ne _ _ _ hNo x hxc]

theorem agreeAt_of_not_tcb {s s' : SystemState} {x : SeLe4n.ObjId} {o : KernelObject}
    (h : (s'.objects[x]?).map KernelObject.withoutRunLinks = (s.objects[x]?).map KernelObject.withoutRunLinks)
    (hNot : ∀ t, o ≠ .tcb t) (hx : s.objects[x]? = some o) : s'.objects[x]? = some o := by
  rw [hx] at h
  cases e : s'.objects[x]? with
  | none => rw [e] at h; cases h
  | some o' =>
      rw [e] at h
      exact congrArg some (KernelObject.withoutRunLinks_eq_of_not_tcb (Option.some.inj h) hNot)

theorem agreeAt_tcb {s s' : SystemState} {x : SeLe4n.ObjId} {t : TCB}
    (h : (s'.objects[x]?).map KernelObject.withoutRunLinks = (s.objects[x]?).map KernelObject.withoutRunLinks)
    (hx : s.objects[x]? = some (.tcb t)) :
    ∃ t', s'.objects[x]? = some (.tcb t') ∧ t'.withoutRunLinks = t.withoutRunLinks := by
  rw [hx] at h
  cases e : s'.objects[x]? with
  | none => rw [e] at h; cases h
  | some o' =>
      rw [e] at h
      obtain ⟨t', rfl, ht⟩ := KernelObject.withoutRunLinks_eq_tcb (Option.some.inj h)
      exact ⟨t', rfl, ht⟩

/-- The reply's writes keep every key where it is found. -/
theorem storeReplyRendezvousReady_keepsFinds (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue)
    (hFC : st.objects.findsInPlace c.toObjId = true) :
    (storeReplyRendezvousReady st c server rid).objectsKeepFinds st := by
  unfold storeReplyRendezvousReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hK1 : (st.updateTcb c receiverReady).objectsKeepFinds st := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact SystemState.mapTcbInPlace_keepsFinds _ _ _
  refine (unlinkReplyWaiter_keepsFinds _ c server).trans ?_
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo3]
  refine (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans ?_
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo2]
  refine (show SystemState.objectsKeepFinds _ _ from
    fun _ => RHTable.findsInPlace_mapValueAt _ _ _ _).trans ?_
  exact (enqueueRunnableOnCore_keepsFinds _ _ c ((hK1 _).trans hFC)).trans hK1

/-- The reply's writes leave its reply object consumed. -/
theorem storeReplyRendezvousReady_reply (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (rp : Reply) (hNo : st.objects.noResizeDue)
    (hT : st.getTcb? c = some ct) (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNe : rid.toObjId ≠ c.toObjId) :
    (storeReplyRendezvousReady st c server rid).objects[rid.toObjId]? = some (.reply rp.consumed) := by
  unfold storeReplyRendezvousReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hT1 : (st.updateTcb c receiverReady).getTcb? c = some (receiverReady ct) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_getTcb?_self, hT]
    rfl
  have hF1 : (st.updateTcb c receiverReady).objects.findsInPlace c.toObjId = true := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact (SystemState.mapTcbInPlace_keepsFinds _ _ _ _).trans hFC
  have hA2 := enqueueRunnableOnCore_agree_of_findsInPlace _
    (determineTargetCore (st.updateTcb c receiverReady) c) c (receiverReady ct) hT1
      (by simp [receiverReady]) hF1
  refine (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ c server).get_reply_iff.mpr ?_
  rw [objects_updateTcb_ne _ _ _ hNo3 _ hNe, objects_modifyObject_self _ _ _ hNo2,
    hA2.get_reply_iff.mpr (by rw [objects_updateTcb_ne _ _ _ hNo _ hNe]; exact hRp)]
  rfl

/-- The answered caller is still a thread after the reply's writes. -/
theorem storeReplyRendezvousReady_caller (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (hNo : st.objects.noResizeDue)
    (hT : st.getTcb? c = some ct) (hFC : st.objects.findsInPlace c.toObjId = true)
    (hNe : rid.toObjId ≠ c.toObjId) :
    ∃ t, (storeReplyRendezvousReady st c server rid).objects[c.toObjId]? = some (.tcb t) := by
  unfold storeReplyRendezvousReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _ (determineTargetCore (st.updateTcb c receiverReady) c)
    c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  have hT1 : (st.updateTcb c receiverReady).getTcb? c = some (receiverReady ct) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_getTcb?_self, hT]
    rfl
  have hF1 : (st.updateTcb c receiverReady).objects.findsInPlace c.toObjId = true := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact (SystemState.mapTcbInPlace_keepsFinds _ _ _ _).trans hFC
  have hA2 := enqueueRunnableOnCore_agree_of_findsInPlace _
    (determineTargetCore (st.updateTcb c receiverReady) c) c (receiverReady ct) hT1
      (by simp [receiverReady]) hF1
  obtain ⟨t2, h2, _⟩ := hA2.get_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT1)
  have h3 : ((enqueueRunnableOnCore (st.updateTcb c receiverReady)
      (determineTargetCore (st.updateTcb c receiverReady) c) c).modifyObject rid.toObjId
        replyConsumedObject).getTcb? c = some t2 :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      (by rw [objects_modifyObject_ne _ _ _ hNo2 _ (fun e => hNe e.symm)]; exact h2)
  have h4 := SystemState.updateTcb_eq_mapTcbInPlace _ c (fun t => { t with replyObjectCode := 0 }) hNo3
  have h4' : (((enqueueRunnableOnCore (st.updateTcb c receiverReady)
      (determineTargetCore (st.updateTcb c receiverReady) c) c).modifyObject rid.toObjId
        replyConsumedObject).updateTcb c (fun t => { t with replyObjectCode := 0 })).objects[c.toObjId]?
        = some (.tcb { t2 with replyObjectCode := 0 }) := by
    rw [h4]
    exact (SystemState.getTcb?_eq_some_iff _ _ _).mp
      (by rw [SystemState.mapTcbInPlace_getTcb?_self, h3]; rfl)
  obtain ⟨t5, h5, _⟩ := (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ c server).get_tcb h4'
  exact ⟨t5, h5⟩

end ReplyFrame

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyRecvInPlace

/-- An object that is not a VSpace root, as `storeLeavesIndexAndTypes` asks. -/
@[inline] def notVSpaceRootAt (s : SystemState) (x : SeLe4n.ObjId) : Bool :=
  match s.objects[x]? with | some (.vspaceRoot _) => false | _ => true

theorem notVSpaceRootAt_eq_view (s : SystemState) (x : SeLe4n.ObjId) :
    notVSpaceRootAt s x =
      match (s.objects[x]?).map KernelObject.withoutRunLinks with
      | some (.vspaceRoot _) => false
      | _ => true := by
  unfold notVSpaceRootAt
  cases s.objects[x]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- **An enqueue's in-place guard carries over** to a state with the same index
and lifecycle, every key found where it was, no new VSpace root and every
thread still a thread. -/
theorem enqueuesInPlace_of_frame {s s' : SystemState} (endpointId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tail? : Option SeLe4n.ThreadId)
    (hI : s'.objectIndexSet = s.objectIndexSet) (hL : s'.lifecycle = s.lifecycle)
    (hK : s'.objectsKeepFinds s)
    (hV : ∀ x, notVSpaceRootAt s x = true → notVSpaceRootAt s' x = true)
    (hTcb : ∀ p : SeLe4n.ThreadId, (s.getTcb? p).isSome = true → (s'.getTcb? p).isSome = true)
    (h : enqueuesInPlace s endpointId tid tail? = true) :
    enqueuesInPlace s' endpointId tid tail? = true := by
  have hS : ∀ {id ty}, storeLeavesIndexAndTypes s id ty = true →
      storeLeavesIndexAndTypes s' id ty = true := by
    intro id ty h
    unfold storeLeavesIndexAndTypes at h ⊢
    rw [hI, hL]
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨h.1, hV id h.2⟩
  unfold enqueuesInPlace at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨⟨⟨⟨⟨h1, hS h2⟩, (hK _).trans h3⟩, hS h4⟩, (hK _).trans h5⟩, ?_⟩
  cases tail? with
  | none => exact h6
  | some p =>
    simp only [Bool.and_eq_true] at h6 ⊢
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h6
    exact ⟨⟨⟨⟨a, b⟩, hS c⟩, (hK _).trans d⟩, hTcb p e⟩

/-- The state after a reply leg whose caller is `c` and whose reply object is
`rid`, holding message `msg`: the facts the receive leg's guard reads, carried
over from the pre-state. -/
theorem storeReplyRendezvous_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    {ep0 : SeLe4n.ObjId} {s? : Option SeLe4n.ThreadId} (hIpc : ct.ipcState = .blockedOnReply ep0 s?)
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hFree : rp.consumed.isFree = true) (hStash : st.replyIsStashed rid = false) :
    (storeReplyRendezvous st c tid rid msg).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt1, (storeReplyRendezvous st c tid rid msg).objects[tid.toObjId]? = some (.tcb rt1) ∧
        receiveBlockAdmits rt1 = true) ∧
      receiveBlocksInPlace (storeReplyRendezvous st c tid rid msg) epId tid ep.receiveQ.tail
        (some rid) = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hHold _ hEc]; exact agreeAt_of_not_tcb (hAg _ hEc hEr) (fun _ e => by cases e) hE
  · obtain ⟨rt1, h1, e1⟩ := agreeAt_tcb (hAg _ hTc' hTr) hR
    refine ⟨rt1, by rw [hHold _ hTc']; exact h1, ?_⟩
    have : receiveBlockAdmits rt1 = receiveBlockAdmits rt1.withoutRunLinks := rfl
    rw [this, e1]; exact hA
  · unfold receiveBlocksInPlace
    rw [Bool.and_eq_true]
    obtain ⟨hI, hL⟩ := storeReplyRendezvousReady_fields st c tid rid hNo
    rw [hS1] at hI hL
    have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
    obtain ⟨tc1, htc1⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
    have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
      hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
    -- every key: the caller and its reply object by name, the rest by agreement
    have hAt : ∀ x, (x = c.toObjId ∧
          ∃ t, (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.tcb t)) ∨
        (x = rid.toObjId ∧
          (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.reply rp.consumed)) ∨
        ((S1.mapTcbInPlace c (holdMessage msg)).objects[x]?).map KernelObject.withoutRunLinks =
          (st.objects[x]?).map KernelObject.withoutRunLinks := by
      intro x
      by_cases hxc : x = c.toObjId
      · subst hxc
        left
        refine ⟨rfl, holdMessage msg tc1, ?_⟩
        rw [SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
      · by_cases hxr : x = rid.toObjId
        · subst hxr; right; left; rw [hHold _ hxc]; exact ⟨rfl, hR1⟩
        · right; right; rw [hHold _ hxc]; exact hAg x hxc hxr
    refine ⟨enqueuesInPlace_of_frame _ _ _ hI hL
      (((SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK)) ?_ ?_ hEnq, ?_⟩
    · intro x hx
      rcases hAt x with ⟨_, t, h⟩ | ⟨_, h⟩ | h
      · unfold notVSpaceRootAt; rw [h]
      · unfold notVSpaceRootAt; rw [h]
      · rw [notVSpaceRootAt_eq_view] at hx ⊢
        rw [h]; exact hx
    · intro p hp
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
      have h1 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
      rcases hAt p.toObjId with ⟨_, t', h⟩ | ⟨e, _⟩ | h
      · exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h⟩
      · rw [e, hRp] at h1; cases h1
      · obtain ⟨t', h', _⟩ := agreeAt_tcb h h1
        exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
    · have hSt : (S1.mapTcbInPlace c (holdMessage msg)).replyIsStashed rid = false := by
        rw [replyIsStashed_of_stashView (st := st) (by
          rw [stashView_hold, ← hS1]
          exact stashView_storeReplyRendezvousReady st c tid rid ct _ _ hNo hTc hIpc) rid]
        exact hStash
      simp only [SystemState.replyStashValid]
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr (by rw [hHold _ hRc]; exact hR1)]
      simp only [hSt, hFree]
      rfl

/-- **The reply-receive that blocks, in place**: under the reply's guard
(`replyWakesInPlace`), with the receiver the server the caller recorded, no
sender waiting and the receive's block admissible (read on the pre-state and
carried across the reply leg, `storeReplyRendezvous_receiveGuard`), the
specification's reply-receive is the reply's writes, the receive's block, the
server's priority walk and the caller's staged message. -/
theorem replyRecvOnCore_blocks_inPlace (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (root : SeLe4n.ObjId) (slot : SeLe4n.Slot) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hCaps : msg.caps = #[])
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hFree : rp.consumed.isFree = true) (hStash : st.replyIsStashed rid = false) :
    endpointReplyRecvOnCore epId tid rid c msg root slot core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (storeReplyRendezvous st c tid rid msg) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.1.2
  obtain ⟨hEq, hHead⟩ := replyOnCore_inPlace st tid c tid ct ep0 rid msg core hSz
    (by rw [hCaps]; decide) hT hIpc hRO hG
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := storeReplyRendezvous_receiveGuard st c tid rid msg ct rp
    epId ep rt hNo hT hIpc hFC hRp hNe hE hR hA hEnq hFree hStash
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRec : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hHead hE1 hR1 hG1
  have hPop : replyRecvPopDonation rid c S1 = .ok (none, S1) := by
    unfold replyRecvPopDonation
    rw [hHead]
  have hEp1 : S1.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE1
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) root slot core S1 =
      (removeRunnableOnCore (storeReceiveBlock S1 epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq S1 epId ep tid rt1 (some rid) core hE1 hS hR1 hA1 hG1]
    have hSnd : (receiveRendezvousSender? S1 epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  unfold endpointReplyRecvOnCore
  simp only [hRec, Option.getD_some, hEq, hPop, hRecv, hEp1, Option.bind_some, hS]
  simp [replyRecvPostReceiveDonation, applyReceiveLegPipHandoff,
    Architecture.stageWokenSendCompletion_none]

end ReplyRecvInPlace

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyRecvDelivered

theorem storeReceiveBlock_noResizeDue (st : SystemState) (epId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tc rc : Nat) (hNo : st.objects.noResizeDue) :
    (storeReceiveBlock st epId tid tc rc).objects.noResizeDue := by
  unfold storeReceiveBlock storeEndpointEnqueue
  dsimp only
  have h1 := modifyObject_noResizeDue st epId
    (enqueueEndpoint true tid (ThreadId.optCode (ThreadId.ofOptCode tc))) hNo
  refine updateTcb_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
    (updateTcb_noResizeDue _ _ _ ?_))
  split
  · exact h1
  · exact updateTcb_noResizeDue _ _ _ h1

theorem storeReceiveBlock_msg (st : SystemState) (epId : SeLe4n.ObjId)
    (tid r : SeLe4n.ThreadId) (tc rc : Nat) (msg : IpcMessage)
    (hNo : st.objects.noResizeDue) (hNe : tid ≠ r) :
    storeReceiveBlock (st.mapTcbInPlace r (holdMessage msg)) epId tid tc rc =
      (storeReceiveBlock st epId tid tc rc).mapTcbInPlace r (holdMessage msg) := by
  unfold storeReceiveBlock storeEndpointEnqueue
  dsimp only
  rw [modifyObject_msg _ _ _ _ _ _ hNo (fun o => by
    cases o <;> try rfl
    generalize ThreadId.optCode (ThreadId.ofOptCode tc) = k
    cases k <;> rfl)]
  have h1 := modifyObject_noResizeDue st epId
    (enqueueEndpoint true tid (ThreadId.optCode (ThreadId.ofOptCode tc))) hNo
  generalize st.modifyObject epId
    (enqueueEndpoint true tid (ThreadId.optCode (ThreadId.ofOptCode tc))) = s1 at h1
  generalize ThreadId.ofOptCode tc = tail?
  have key : ∀ s2 : SystemState, s2.objects.noResizeDue →
      (((s2.mapTcbInPlace r (TCB.withMessageSlots id (fun _ => some msg) id)).updateTcb tid
        (enqueueLinks tail?)).updateTcb tid
        (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId))).updateTcb
        tid (fun t => { t with pendingReceiveReplyCode := rc }) =
      (((s2.updateTcb tid (enqueueLinks tail?)).updateTcb tid
        (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId))).updateTcb
        tid (fun t => { t with pendingReceiveReplyCode := rc })).mapTcbInPlace r
        (TCB.withMessageSlots id (fun _ => some msg) id) := by
    intro s2 hNo2
    rw [updateTcb_msg _ _ _ _ _ _ (enqueueLinks tail?) hNo2
      (fun _ _ => by cases tail? <;> rfl)]
    have hNo3 := updateTcb_noResizeDue s2 tid (enqueueLinks tail?) hNo2
    rw [updateTcb_msg _ _ _ _ _ _
      (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId)) hNo3
      (fun h => absurd h hNe)]
    rw [updateTcb_msg _ _ _ _ _ _ (fun t => { t with pendingReceiveReplyCode := rc })
      (updateTcb_noResizeDue _ _ _ hNo3) (fun _ _ => rfl)]
  cases tail? with
  | none => exact key s1 h1
  | some p =>
    simp only []
    rw [updateTcb_msg _ _ _ _ _ _ (tcbWithQueueNext tid) h1 (fun _ _ => rfl)]
    exact key _ (updateTcb_noResizeDue _ _ _ h1)

/-- Every thread of `s` is a thread of `s'` in the same IPC state. -/
def ipcStateCarried (s s' : SystemState) : Prop :=
  ∀ (t : SeLe4n.ThreadId) (x : TCB), s.getTcb? t = some x →
    ∃ x', s'.getTcb? t = some x' ∧ x'.ipcState = x.ipcState

theorem ipcStateCarried.trans {s s' s'' : SystemState} (h1 : ipcStateCarried s s')
    (h2 : ipcStateCarried s' s'') : ipcStateCarried s s'' := by
  intro t x hx
  obtain ⟨x', h', e'⟩ := h1 t x hx
  obtain ⟨x'', h'', e''⟩ := h2 t x' h'
  exact ⟨x'', h'', e''.trans e'⟩

theorem ipcStateCarried_of_agree {s s' : SystemState} (h : s'.objectsAgreeOffRunLinks s) :
    ipcStateCarried s s' := by
  intro t x hx
  obtain ⟨x', h', e⟩ := h.getTcb?_some hx
  exact ⟨x', h', TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState e⟩

theorem ipcStateCarried_of_objects_eq {s s' : SystemState} (h : s'.objects = s.objects) :
    ipcStateCarried s s' := by
  intro t x hx
  refine ⟨x, ?_, rfl⟩
  unfold SystemState.getTcb? at hx ⊢
  rw [h]; exact hx

theorem ipcStateCarried_mapTcbInPlace (s : SystemState) (r : SeLe4n.ThreadId) (g : TCB → TCB)
    (hg : ∀ x, (g x).ipcState = x.ipcState) : ipcStateCarried s (s.mapTcbInPlace r g) := by
  intro t x hx
  by_cases e : r.toObjId = t.toObjId
  · have := SeLe4n.ThreadId.toObjId_injective _ _ e
    subst this
    exact ⟨g x, by rw [SystemState.mapTcbInPlace_getTcb?_self, hx]; rfl, hg x⟩
  · exact ⟨x, by rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ e]; exact hx, rfl⟩

theorem updatePipBoostOnCore_ipcStateCarried (s : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hNo : s.objects.noResizeDue) :
    ipcStateCarried s (PriorityInheritance.updatePipBoostOnCore s c t) := by
  rw [PriorityInheritance.updatePipBoostOnCore_eq_impl]
  unfold PriorityInheritance.updatePipBoostOnCoreImpl
  split
  · dsimp only
    split
    · exact fun _ x hx => ⟨x, hx, rfl⟩
    · rw [SystemState.updateTcb_eq_mapTcbInPlace s t
        (fun x => { x with pipBoostCode := PriorityInheritance.computeMaxWaiterCode s t }) hNo]
      refine ((ipcStateCarried_mapTcbInPlace s t
        (fun x => { x with pipBoostCode := PriorityInheritance.computeMaxWaiterCode s t })
        (fun _ => rfl)).trans ?_).trans
        (ipcStateCarried_of_objects_eq (markKeyChangeParts_objects _ _ _ _ _))
      split
      · exact ipcStateCarried_of_agree
          (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ _ _ _)
      · exact fun _ x hx => ⟨x, hx, rfl⟩
  · exact fun _ x hx => ⟨x, hx, rfl⟩

theorem propagatePipChainCrossCore_ipcStateCarried (s : SystemState) (t : SeLe4n.ThreadId)
    (ec : CoreId) (hNo : s.objects.noResizeDue) :
    ipcStateCarried s (PriorityInheritance.propagatePipChainCrossCore s t ec).1 := by
  rw [PriorityInheritance.propagatePipChainCrossCore_eq_walks]
  dsimp only
  generalize s.objectIndex.length = fuel
  induction fuel generalizing s t with
  | zero => exact fun _ x hx => ⟨x, hx, rfl⟩
  | succ n ih =>
    unfold PriorityInheritance.propagatePipChainStateWalk
    split
    · exact (updatePipBoostOnCore_ipcStateCarried s _ t hNo).trans
        (ih _ _ (updatePipBoostOnCore_noResizeDue _ _ _ hNo))
    · exact updatePipBoostOnCore_ipcStateCarried s _ t hNo

/-- The reply-receive that blocks, its caller woken holding no message: the
reply's writes, the server's block on the endpoint, then its priority walk. -/
@[noinline] def storeReplyRecvBlockReady (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) :
    SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore
    (removeRunnableOnCore (storeReceiveBlock (storeReplyRendezvousReady st c tid rid) epId tid
      tailCode (rid.val + 1)) tid core) tid core).1

theorem storeReplyRecvBlockReady_noResizeDue (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : st.objects.noResizeDue) :
    (storeReplyRecvBlockReady st c tid rid epId tailCode core).objects.noResizeDue :=
  propagatePipChainCrossCore_noResizeDue _ _ _ (removeRunnableOnCore_noResizeDue _ _ _
    (storeReceiveBlock_noResizeDue _ _ _ _ _ (storeReplyRendezvousReady_noResizeDue _ _ _ _ hNo)))

/-- **The blocking reply-receive's staged caller is its delivered one**: the
message held by the reply leg commutes out past the receive's block and the
priority walk, and staging it is writing its frame. -/
theorem replyRecvBlock_staged (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (msg : IpcMessage) (hNo : st.objects.noResizeDue) (hNe : tid ≠ c)
    (hSz : msg.registers.size ≤ 4) :
    Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (storeReplyRendezvous st c tid rid msg) epId tid
            tailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0 =
      writeDeliveredFrameIfReady (storeReplyRecvBlockReady st c tid rid epId tailCode core) c
        (Architecture.returnFrameOfMessage msg 0 0)
        (fun _ => (storeReplyRecvBlockReady st c tid rid epId tailCode core).mapTcbInPlace c
          (holdMessage msg)) := by
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have h2 := storeReceiveBlock_noResizeDue _ epId tid tailCode (SeLe4n.ReplyId.optCode (some rid)) h1
  have h3 := removeRunnableOnCore_noResizeDue _ tid core h2
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, storeReceiveBlock_msg _ _ _ _ _ _ _ h1 hNe,
    removeRunnableOnCore_msg, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ h3,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ h3) hSz]
  rfl

/-- Staging a thread other than the one a delivered frame is written to is the
identity when that thread is blocked. -/
theorem stageDeliveredMessage_writeDeliveredFrameIfReady_blocked (X : SystemState)
    (r t : SeLe4n.ThreadId) (f : Architecture.SyscallReturnFrame) (g : TCB → TCB) (n : Nat)
    (hNe : r.toObjId ≠ t.toObjId) (x : TCB) (hT : X.getTcb? t = some x)
    (hB : x.ipcState ≠ .ready) :
    Architecture.stageDeliveredMessage
        (writeDeliveredFrameIfReady X r f (fun _ => X.mapTcbInPlace r g)) t n =
      writeDeliveredFrameIfReady X r f (fun _ => X.mapTcbInPlace r g) := by
  apply Architecture.stageDeliveredMessage_id_when_blocked _ _ _ x _ hB
  unfold writeDeliveredFrameIfReady
  split
  · split
    · rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe]; exact hT
    · rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe]; exact hT
  · exact hT

/-- **The blocking reply-receive, delivered**: under the in-place guard of
`replyRecvOnCore_blocks_inPlace` and a reply of at most four words, the checked
arm's result is the caller's frame written into its saved registers on top of
`storeReplyRecvBlockReady`; the server, blocked on the endpoint, stages
nothing. -/
theorem replyRecvOnCore_blocks_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (root : SeLe4n.ObjId) (slot : SeLe4n.Slot) (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hCaps : msg.caps = #[])
    (hSz4 : msg.registers.size ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hFree : rp.consumed.isFree = true) (hStash : st.replyIsStashed rid = false) :
    (match endpointReplyRecvOnCore epId tid rid c msg root slot core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.installedCount) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), writeDeliveredFrameIfReady
        (storeReplyRecvBlockReady st c tid rid epId ep.recvTailCode core) c
        (Architecture.returnFrameOfMessage msg 0 0)
        (fun _ => (storeReplyRecvBlockReady st c tid rid epId ep.recvTailCode core).mapTcbInPlace c
          (holdMessage msg))) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.1.2
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  rw [replyRecvOnCore_blocks_inPlace st epId tid c rid msg root slot core ct ep0 rt ep rp hSz hCaps
    hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hFree hStash]
  simp only [CapTransferSummary.installedCount_empty]
  rw [replyRecvBlock_staged _ _ _ _ _ _ _ _ hNo hNe hSz4]
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := storeReplyRendezvous_receiveGuard st c tid rid msg ct rp
    epId ep rt hNo hT hIpc hFC hRp hNe hE hR hA hEnq hFree hStash
  obtain ⟨t, hT1, hB⟩ := receiveBlock_receiver_blocked _ epId ep tid rt1 (some rid) core hE1 hR1
    hA1 hG1
  have h1 := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have h3 := removeRunnableOnCore_noResizeDue _ tid core
    (storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid)) h1)
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, storeReceiveBlock_msg _ _ _ _ _ _ _ h1 hNe,
    removeRunnableOnCore_msg, SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h3 tid t hT1
  rw [stageDeliveredMessage_writeDeliveredFrameIfReady_blocked
    (storeReplyRecvBlockReady st c tid rid epId ep.recvTailCode core) c tid _ _ 0 hCT x hX
    (by rw [hEq, hB]; exact fun h => by cases h)]

/-- The fallback of a reply-receive's delivery: the reply's message built and
held, as the specification holds it.  Out of line, so the message record is
built only on this path. -/
@[noinline] def holdReplyRecvBody (X : SystemState) (c : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  X.mapTcbInPlace c (holdMessage
    { registers := Architecture.regReplyRecvBody layout rf len, caps := #[], badge := badge })

/-- **The blocking reply-receive, delivered from the registers**: the reply's
writes, the server's block and priority walk, then the reply's frame written
into the caller's saved registers.  The message is built only where the caller
is, unexpectedly, not ready. -/
@[noinline] def performReplyRecvBlockDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId) : SystemState :=
  let X := storeReplyRecvBlockReady st c tid rid epId tailCode core
  writeDeliveredFrameIfReady X c (Architecture.regReplyRecvFrame layout rf len badge)
    (fun _ => holdReplyRecvBody X c layout rf len badge)

end ReplyRecvDelivered

end SeLe4n.Kernel
