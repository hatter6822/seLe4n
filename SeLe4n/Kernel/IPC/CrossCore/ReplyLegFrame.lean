/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv
import SeLe4n.Kernel.IPC.CrossCore.ReceiveReturnInPlace

/-!
# The reply leg's frame

What the in-place reply leg (`storeReplyRendezvousReady`) writes and keeps:
the caller woken and its reply object consumed, every other object agreeing
off its run-queue links (`storeReplyRendezvousReady_agree`), the stasher test
read through the frame (`stasherTestAt`), and the IPC state a later write
carries (`ipcStateCarried`).  The reply, the reply-receive's legs and the
take arms read these facts; the reply-receive's own leg equalities are
`ReplyRecvBlockComposed`'s.
-/

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

/-- **Off the answered caller and its reply object, the reply's writes touch
only links.** -/
theorem storeReplyRendezvousReady_agree (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (ct : TCB) (hNo : st.objects.noResizeDue)
    (hT : st.getTcb? c = some ct) (hFC : st.objects.findsInPlace c.toObjId = true)
    (x : SeLe4n.ObjId) (hxc : x ≠ c.toObjId) (hxr : x ≠ rid.toObjId) :
    ((storeReplyRendezvousReady st c server rid).objects[x]?).map KernelObject.withoutRunLinks =
      (st.objects[x]?).map KernelObject.withoutRunLinks := by
  unfold storeReplyRendezvousReady storeReplyLegReady
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
  unfold storeReplyRendezvousReady storeReplyLegReady
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
  unfold storeReplyRendezvousReady storeReplyLegReady
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
    ∃ t, (storeReplyRendezvousReady st c server rid).objects[c.toObjId]? = some (.tcb t) ∧
      t.ipcStateCode = (receiverReady ct).ipcStateCode := by
  unfold storeReplyRendezvousReady storeReplyLegReady
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
  obtain ⟨t2, h2, e2⟩ := hA2.get_tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT1)
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
  obtain ⟨t5, h5, e5⟩ := (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ c server).get_tcb h4'
  refine ⟨t5, h5, ?_⟩
  have a5 := congrArg TCB.ipcStateCode e5
  have a2 := congrArg TCB.ipcStateCode e2
  simp only [TCB.withoutRunLinks] at a5 a2
  rw [a5]; exact a2

end ReplyFrame

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyRecvInPlace

/-- Objects that agree off their run-queue links are of the same kind.  WS-UC
UC2: the kind at each key is what `storeLeavesIndexAndTypes` reads. -/
theorem getObjectType?_of_view {s s' : SystemState} {x : SeLe4n.ObjId}
    (h : (s'.objects[x]?).map KernelObject.withoutRunLinks =
      (s.objects[x]?).map KernelObject.withoutRunLinks) :
    s'.getObjectType? x = s.getObjectType? x := by
  have e := congrArg (Option.map KernelObject.objectType) h
  simp only [Option.map_map, Function.comp_def, KernelObject.objectType_withoutRunLinks] at e
  unfold SystemState.getObjectType?
  exact e

/-- A store-locality answer carries over to a state whose every key holds an
object of the same kind (WS-UC UC2: the answer reads only the kinds). -/
theorem storeLeavesIndexAndTypes_of_frame {s s' : SystemState}
    (hK : ∀ x, s'.getObjectType? x = s.getObjectType? x)
    {id : SeLe4n.ObjId} {ty : KernelObjectType} (h : storeLeavesIndexAndTypes s id ty = true) :
    storeLeavesIndexAndTypes s' id ty = true := by
  have e := hK id
  unfold SystemState.getObjectType? at e
  unfold storeLeavesIndexAndTypes storeKeepsKind at h ⊢
  cases h1 : s.objects[id]? with
  | none => rw [h1] at h; simp at h
  | some o =>
    cases h2 : s'.objects[id]? with
    | none => rw [h1, h2] at e; cases e
    | some o' =>
      rw [h1, h2] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [h1] at h; simp only [] at h ⊢
      rw [e]; exact h

/-- **The stasher test of one key**: the thread there is blocked receiving with
reply code `n` as its stash — what `SystemState.replyStashedAt` asks of the
thread a Reply records. -/
@[inline] def stasherTestAt (s : SystemState) (x : SeLe4n.ThreadId) (n : Nat) : Bool :=
  match s.getTcb? x with
  | some t => t.ipcStateCode == 1 && t.pendingReceiveReplyCode == n
  | none => false

theorem replyStashedAt_eq_stasherTestAt (s : SystemState) (rid : SeLe4n.ReplyId) (r : Reply) :
    s.replyStashedAt rid r = (match r.stasherCode with
      | 0 => false
      | k + 1 => stasherTestAt s (⟨k⟩ : SeLe4n.ThreadId) (rid.val + 1)) := by
  unfold SystemState.replyStashedAt stasherTestAt
  rfl

/-- Objects that agree off their run-queue links agree on the stasher test: it
reads a thread's state and stash codes, which no run-queue link holds. -/
theorem stasherTestAt_of_view {s s' : SystemState} {x : SeLe4n.ThreadId}
    (h : (s'.objects[x.toObjId]?).map KernelObject.withoutRunLinks =
      (s.objects[x.toObjId]?).map KernelObject.withoutRunLinks) (n : Nat) :
    stasherTestAt s' x n = stasherTestAt s x n := by
  unfold stasherTestAt SystemState.getTcb?
  cases e : s.objects[x.toObjId]? with
  | none =>
    rw [e] at h
    cases e' : s'.objects[x.toObjId]? with
    | none => rfl
    | some _ => rw [e'] at h; cases h
  | some o =>
    cases o with
    | tcb t =>
      obtain ⟨t', h', e1⟩ := agreeAt_tcb h e
      rw [h']
      have a := congrArg TCB.ipcStateCode e1
      have b := congrArg TCB.pendingReceiveReplyCode e1
      simp only [TCB.withoutRunLinks] at a b
      simp only [a, b]
    | _ =>
      rw [agreeAt_of_not_tcb h (fun _ e => by cases e) e]

/-- **An enqueue's in-place guard carries over** to a state with every key found
where it was, every key holding an object of the same kind and every thread
still a thread. -/
theorem enqueuesInPlace_of_frame {s s' : SystemState} (endpointId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tail? : Option SeLe4n.ThreadId)
    (hK : s'.objectsKeepFinds s)
    (hV : ∀ x, s'.getObjectType? x = s.getObjectType? x)
    (hTcb : ∀ p : SeLe4n.ThreadId, (s.getTcb? p).isSome = true → (s'.getTcb? p).isSome = true)
    (h : enqueuesInPlace s endpointId tid tail? = true) :
    enqueuesInPlace s' endpointId tid tail? = true := by
  have hS : ∀ {id ty}, storeLeavesIndexAndTypes s id ty = true →
      storeLeavesIndexAndTypes s' id ty = true :=
    fun h => storeLeavesIndexAndTypes_of_frame hV h
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

/-- **The receive's block guard carries across the return** (seL4-MCS
`receiveIPC`'s `maybeReturnSchedContext`, run before the endpoint is looked at):
the return clears a thread's two binding codes and rewrites a context, so the
endpoint, every slot's kind and finding, every stash test and the receiver's
admission read the same after it.  The receiver's binding goes from `.bound`
to `.unbound`, which a blocking receive admits. -/
theorem receiveReturnSchedContext_receiveGuard (blocks : Bool) (S : SystemState)
    (tid : SeLe4n.ThreadId) {epId : SeLe4n.ObjId} {ep : Endpoint} {rt : TCB}
    {tail? : Option SeLe4n.ThreadId} {rid? : Option SeLe4n.ReplyId}
    (hNo : S.objects.noResizeDue)
    (hE : S.objects[epId]? = some (.endpoint ep))
    (hR : S.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hG : receiveBlocksInPlace S epId tid tail? rid? = true) :
    (receiveReturnSchedContext blocks S tid).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt', (receiveReturnSchedContext blocks S tid).objects[tid.toObjId]? = some (.tcb rt') ∧
        receiveBlockAdmits rt' = true) ∧
      receiveBlocksInPlace (receiveReturnSchedContext blocks S tid) epId tid tail? rid? = true := by
  have hAg := receiveReturnSchedContext_returnAgree blocks S tid hNo
  have hKF := receiveReturnSchedContext_keepsFinds blocks S tid hNo
  generalize receiveReturnSchedContext blocks S tid = S' at hAg hKF
  -- every slot keeps its kind
  have hV : ∀ x, S'.getObjectType? x = S.getObjectType? x := by
    intro x
    unfold SystemState.getObjectType?
    rcases hAg x with e | ⟨o, o', h0, h1, r⟩
    · rw [e]
    · rw [h0, h1]
      rcases r with rfl | ⟨t, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;> rfl
  -- a slot that is not a thread or a context is unchanged
  have hOther : ∀ (x : SeLe4n.ObjId) (o : KernelObject), S.objects[x]? = some o → (∀ t, o ≠ .tcb t) →
      (∀ sc, o ≠ KernelObject.schedContext sc) → S'.objects[x]? = some o := by
    intro x o h hT hS
    rcases hAg x with e | ⟨o0, o', h0, h1, r⟩
    · rw [e, h]
    · rw [h] at h0; cases h0
      rcases r with rfl | ⟨t, rfl, _⟩ | ⟨sc, _, rfl, _⟩
      · exact h1
      · exact absurd rfl (hT t)
      · exact absurd rfl (hS sc)
  -- a thread is a thread with the same IPC words
  have hTcb : ∀ (p : SeLe4n.ThreadId) (t : TCB), S.objects[p.toObjId]? = some (.tcb t) →
      ∃ t', S'.objects[p.toObjId]? = some (.tcb t') ∧
        (t' = t ∨ t' = { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) := by
    intro p t h
    rcases hAg p.toObjId with e | ⟨o0, o', h0, h1, r⟩
    · exact ⟨t, by rw [e, h], Or.inl rfl⟩
    · rw [h] at h0; cases h0
      rcases r with rfl | ⟨t1, e1, rfl⟩ | ⟨_, _, e1, _⟩
      · exact ⟨t, h1, Or.inl rfl⟩
      · cases e1; exact ⟨_, h1, Or.inr rfl⟩
      · cases e1
  have hBack : ∀ (p : SeLe4n.ThreadId) (t' : TCB), S'.objects[p.toObjId]? = some (.tcb t') →
      ∃ t, S.objects[p.toObjId]? = some (.tcb t) := by
    intro p t' h
    rcases hAg p.toObjId with e | ⟨o0, o', h0, h1, r⟩
    · exact ⟨t', by rw [← e, h]⟩
    · rw [h] at h1; cases h1
      rcases r with e1 | ⟨t1, e1, _⟩ | ⟨_, _, _, e2⟩
      · subst e1; exact ⟨t', h0⟩
      · exact ⟨t1, by rw [h0, e1]⟩
      · cases e2
  have hStash : ∀ (x : SeLe4n.ThreadId) n, stasherTestAt S' x n = stasherTestAt S x n := by
    intro x n
    unfold stasherTestAt SystemState.getTcb?
    cases e : S.objects[x.toObjId]? with
    | none =>
      cases e' : S'.objects[x.toObjId]? with
      | none => rfl
      | some o' =>
        cases o' with
        | tcb t' => obtain ⟨t, h⟩ := hBack x t' e'; rw [e] at h; cases h
        | _ => rfl
    | some o =>
      cases o with
      | tcb t =>
        obtain ⟨t', h', r⟩ := hTcb x t e
        rw [h']
        rcases r with rfl | rfl <;> rfl
      | schedContext sc =>
        rcases hAg x.toObjId with e' | ⟨o0, o', h0, h1, r⟩
        · rw [e', e]
        · rw [e] at h0; cases h0
          rcases r with rfl | ⟨_, e1, _⟩ | ⟨_, _, _, rfl⟩
          · rw [h1]
          · cases e1
          · rw [h1]
      | _ =>
        rw [hOther _ _ e (fun _ h => by cases h) (fun _ h => by cases h)]
  refine ⟨hOther _ _ hE (fun _ h => by cases h) (fun _ h => by cases h), ?_, ?_⟩
  · obtain ⟨rt', h', r⟩ := hTcb tid rt hR
    refine ⟨rt', h', ?_⟩
    rcases r with rfl | rfl
    · exact hA
    · simp only [receiveBlockAdmits, Bool.and_eq_true] at hA ⊢
      exact ⟨hA.1, rfl⟩
  · unfold receiveBlocksInPlace at hG ⊢
    simp only [Bool.and_eq_true] at hG ⊢
    obtain ⟨⟨hEnq, hSt⟩, hRec⟩ := hG
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ hKF hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
      obtain ⟨t', h', _⟩ := hTcb p t ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht)
      exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
    · revert hSt
      cases rid? with
      | none => intro _; rfl
      | some rid =>
        simp only [SystemState.replyStashValid]
        cases hr : S.getReply? rid with
        | none => intro e; cases e
        | some r =>
          intro hs
          have h1 := hOther _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hr)
            (fun _ h => by cases h) (fun _ h => by cases h)
          rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr h1]
          dsimp only at hs ⊢
          rw [replyStashedAt_eq_stasherTestAt] at hs ⊢
          revert hs
          cases r.stasherCode with
          | zero => exact id
          | succ k => dsimp only; rw [hStash]; exact id
    · revert hRec
      cases rid? with
      | none => exact id
      | some rid =>
        simp only [SeLe4n.ReplyId.optCode, replyRecordsInPlace, Bool.and_eq_true]
        rintro ⟨a, b⟩
        exact ⟨(hKF _).trans a, storeLeavesIndexAndTypes_of_frame hV b⟩

end ReplyRecvInPlace

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section ReplyRecvDelivered

theorem storeReplyStasher_noResizeDue (st : SystemState) (rc : Nat) (recv : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) : (storeReplyStasher st rc recv).objects.noResizeDue := by
  rcases rc with _ | k
  · exact hNo
  · exact modifyObject_noResizeDue _ _ _ hNo

/-- The stasher record commutes with a message-slot write: it rewrites one
Reply, which holds no message slot. -/
theorem storeReplyStasher_msg (st : SystemState) (r recv : SeLe4n.ThreadId) (rc : Nat)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat)
    (hNo : st.objects.noResizeDue) :
    storeReplyStasher (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) rc recv =
      (storeReplyStasher st rc recv).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rcases rc with _ | k
  · rfl
  · exact modifyObject_msg _ _ _ _ _ _ hNo (fun o => by cases o <;> rfl)

theorem storeReceiveBlock_noResizeDue (st : SystemState) (epId : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (tc rc : Nat) (hNo : st.objects.noResizeDue) :
    (storeReceiveBlock st epId tid tc rc).objects.noResizeDue := by
  unfold storeReceiveBlock
  simp only [storeEndpointEnqueueCode_eq]
  unfold storeEndpointEnqueue
  dsimp only
  have h1 := modifyObject_noResizeDue st epId
    (enqueueEndpoint true tid (ThreadId.optCode (ThreadId.ofOptCode tc))) hNo
  refine updateTcb_noResizeDue _ _ _ (storeReplyStasher_noResizeDue _ _ _
    (updateTcb_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ ?_)))
  split
  · exact h1
  · exact updateTcb_noResizeDue _ _ _ h1

theorem storeReceiveBlock_msg (st : SystemState) (epId : SeLe4n.ObjId)
    (tid r : SeLe4n.ThreadId) (tc rc : Nat) (msg : IpcMessage)
    (hNo : st.objects.noResizeDue) (hNe : tid ≠ r) :
    storeReceiveBlock (st.mapTcbInPlace r (holdMessage msg)) epId tid tc rc =
      (storeReceiveBlock st epId tid tc rc).mapTcbInPlace r (holdMessage msg) := by
  unfold storeReceiveBlock
  simp only [storeEndpointEnqueueCode_eq]
  unfold storeEndpointEnqueue
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
      (storeReplyStasher (((s2.mapTcbInPlace r (TCB.withMessageSlots id (fun _ => some msg) id)).updateTcb tid
        (enqueueLinks tail?)).updateTcb tid
        (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId))) rc tid).updateTcb
        tid (fun t => { t with pendingReceiveReplyCode := rc }) =
      ((storeReplyStasher ((s2.updateTcb tid (enqueueLinks tail?)).updateTcb tid
        (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId))) rc tid).updateTcb
        tid (fun t => { t with pendingReceiveReplyCode := rc })).mapTcbInPlace r
        (TCB.withMessageSlots id (fun _ => some msg) id) := by
    intro s2 hNo2
    rw [updateTcb_msg _ _ _ _ _ _ (enqueueLinks tail?) hNo2
      (fun _ _ => by cases tail? <;> rfl)]
    have hNo3 := updateTcb_noResizeDue s2 tid (enqueueLinks tail?) hNo2
    rw [updateTcb_msg _ _ _ _ _ _
      (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId)) hNo3
      (fun h => absurd h hNe)]
    have hNo4 := updateTcb_noResizeDue _ tid
      (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnReceive epId)) hNo3
    rw [storeReplyStasher_msg _ _ _ _ _ _ _ hNo4]
    rw [updateTcb_msg _ _ _ _ _ _ (fun t => { t with pendingReceiveReplyCode := rc })
      (storeReplyStasher_noResizeDue _ _ _ hNo4) (fun _ _ => rfl)]
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
  generalize s.objects.size = fuel
  induction fuel generalizing s t with
  | zero => exact fun _ x hx => ⟨x, hx, rfl⟩
  | succ n ih =>
    unfold PriorityInheritance.propagatePipChainStateWalk
    split
    · exact (updatePipBoostOnCore_ipcStateCarried s _ t hNo).trans
        (ih _ _ (updatePipBoostOnCore_noResizeDue _ _ _ hNo))
    · exact updatePipBoostOnCore_ipcStateCarried s _ t hNo

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

/-- The fallback of a reply-receive's delivery: the reply's message built and
held, as the specification holds it.  Out of line, so the message record is
built only on this path. -/
@[noinline] def holdReplyRecvBody (X : SystemState) (c : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  X.mapTcbInPlace c (holdMessage
    { registers := Architecture.regMessageBody layout rf len, badge := badge })

end ReplyRecvDelivered

end SeLe4n.Kernel
