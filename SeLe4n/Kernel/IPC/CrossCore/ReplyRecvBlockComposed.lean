/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReplyLegFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyPopFrame
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyHeldInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyUnheldPopFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyCapsReturnDelivered
import SeLe4n.Kernel.IPC.CrossCore.LongFaultAnswerInPlace

/-!
# The blocking reply-receive, composed over its reply arm

WS-SX SX25.  A reply-receive whose receive leg blocks runs one reply leg, one
pop and one block, whatever the reply's arm: the reply's writes
(`storeReplyRendezvous` when the caller recorded the server,
`storeReplyLeg` when it recorded none), the arm's pop (none, the donated pop
and its settle, the held pop, the unheld pop and its settle, or none on a reply
linked to nothing), the server's context return on its bound notification, its
block on the endpoint, its removal from its core (and, on the donated arm, its
deschedule from the context it gave back), then its priority walk.  The arm is
data (`ReplyRecvArm`), so the shapes the receive answers (the short and the
long message, the capability transfer, the fault) are each written once over
it, and joined to the specification through one equality per arm
(`replyRecvAnsweringOnCore_arm_inPlace`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ## The receive leg's guard across the caller's fault answer

The fault answer (`faultReplyApplyOnCore`) writes the caller's own TCB — its
restart frame, its fault record, its thread state — and, on an abandon, takes
it off its core's run queue, which rewrites its neighbours' run-queue links.
None of that is read by the receive leg's guard: the caller's slot keeps its
kind and its stash codes, every other slot keeps everything off its run-queue
links.  So the receive, run after the answer as seL4's `doReplyTransfer` runs
before `handleRecv` (WS-SX SX32), is guarded as it was before it. -/

/-- What the caller's fault answer leaves of the state the receive's guards
read: the table's finds; every slot but the caller's off its run-queue links;
the caller's slot the same off its run-queue links, or a TCB keeping its
`ipcStateCode` and `pendingReceiveReplyCode`. -/
def answerGuardFrame (c : SeLe4n.ThreadId) (s' s : SystemState) : Prop :=
  s'.objectsKeepFinds s ∧
    (∀ x, x ≠ c.toObjId → (s'.objects[x]?).map KernelObject.withoutRunLinks =
      (s.objects[x]?).map KernelObject.withoutRunLinks) ∧
    ((s'.objects[c.toObjId]?).map KernelObject.withoutRunLinks =
        (s.objects[c.toObjId]?).map KernelObject.withoutRunLinks ∨
      ∃ t t', s.objects[c.toObjId]? = some (.tcb t) ∧ s'.objects[c.toObjId]? = some (.tcb t') ∧
        t'.ipcStateCode = t.ipcStateCode ∧ t'.pendingReceiveReplyCode = t.pendingReceiveReplyCode)

theorem answerGuardFrame_of_offRunLinks {c : SeLe4n.ThreadId} {s' s : SystemState}
    (hK : s'.objectsKeepFinds s) (h : s'.objectsAgreeOffRunLinks s) : answerGuardFrame c s' s :=
  ⟨hK, fun x _ => h x, .inl (h _)⟩

/-- A run-queue-only step, then a caller write: the frame composes. -/
theorem answerGuardFrame.trans_offRunLinks {c : SeLe4n.ThreadId} {a b d : SystemState}
    (h₂ : answerGuardFrame c d b) (hK : b.objectsKeepFinds a) (h₁ : b.objectsAgreeOffRunLinks a) :
    answerGuardFrame c d a := by
  refine ⟨h₂.1.trans hK, fun x hx => (h₂.2.1 x hx).trans (h₁ x), ?_⟩
  rcases h₂.2.2 with h | ⟨t, t', ht, ht', e1, e2⟩
  · exact .inl (h.trans (h₁ _))
  · obtain ⟨t0, h0, e0⟩ := agreeAt_tcb (h₁ c.toObjId).symm ht
    refine .inr ⟨t0, t', h0, ht', ?_, ?_⟩
    · rw [e1]; exact (congrArg TCB.ipcStateCode e0).symm
    · rw [e2]; exact (congrArg TCB.pendingReceiveReplyCode e0).symm

/-- A write to the caller's TCB keeping its stash codes. -/
theorem answerGuardFrame_mapTcbInPlace (s : SystemState) (c : SeLe4n.ThreadId) (g : TCB → TCB)
    (hC : ∀ t, (g t).ipcStateCode = t.ipcStateCode)
    (hP : ∀ t, (g t).pendingReceiveReplyCode = t.pendingReceiveReplyCode) :
    answerGuardFrame c (s.mapTcbInPlace c g) s := by
  refine ⟨SystemState.mapTcbInPlace_keepsFinds _ _ _, fun x hx => ?_, ?_⟩
  · rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  · rw [SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _)]
    cases e : s.objects[c.toObjId]? with
    | none => exact .inl rfl
    | some o =>
      cases o with
      | tcb t => exact .inr ⟨t, g t, rfl, rfl, hC t, hP t⟩
      | _ => exact .inl rfl

/-- **The caller's fault answer keeps what the receive's guards read.** -/
theorem faultReplyApplyOnCore_answerGuardFrame (s : SystemState) (c : SeLe4n.ThreadId)
    (f : Architecture.FaultReplyOutcome) (hNo : s.objects.noResizeDue) :
    answerGuardFrame c (faultReplyApplyOnCore s c f) s ∧
      (faultReplyApplyOnCore s c f).objects.noResizeDue := by
  cases f with
  | restart frame =>
    show answerGuardFrame c (applyFaultRestart s c frame) s ∧
      (applyFaultRestart s c frame).objects.noResizeDue
    unfold applyFaultRestart
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
    exact ⟨answerGuardFrame_mapTcbInPlace s c _ (fun _ => rfl) (fun _ => rfl), hNo⟩
  | abandon =>
    show answerGuardFrame c (faultAbandonOnCore s c (faultAbandonCore s c)) s ∧
      (faultAbandonOnCore s c (faultAbandonCore s c)).objects.noResizeDue
    unfold faultAbandonOnCore
    have hNo1 := removeRunnableOnCore_noResizeDue s c (faultAbandonCore s c) hNo
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1]
    refine ⟨?_, hNo1⟩
    exact (answerGuardFrame_mapTcbInPlace _ c
      (fun tcb => { tcb.setPendingFault none with threadState := .Inactive })
      (fun _ => rfl) (fun _ => rfl)).trans_offRunLinks
      (removeRunnableOnCore_keepsFinds s c _) (removeRunnableOnCore_objectsAgreeOffRunLinks s c _)

namespace answerGuardFrame

variable {c : SeLe4n.ThreadId} {s' s : SystemState}

/-- Every slot keeps its kind. -/
theorem getObjectType? (h : answerGuardFrame c s' s) (x : SeLe4n.ObjId) :
    s'.getObjectType? x = s.getObjectType? x := by
  by_cases hx : x = c.toObjId
  · subst hx
    rcases h.2.2 with e | ⟨t, t', ht, ht', -, -⟩
    · exact getObjectType?_of_view e
    · unfold SystemState.getObjectType?; rw [ht, ht']; rfl
  · exact getObjectType?_of_view (h.2.1 x hx)

/-- An object other than a TCB is kept. -/
theorem obj (h : answerGuardFrame c s' s) {x : SeLe4n.ObjId} {o : KernelObject}
    (hNot : ∀ t, o ≠ .tcb t) (hx : s.objects[x]? = some o) : s'.objects[x]? = some o := by
  by_cases hc : x = c.toObjId
  · subst hc
    rcases h.2.2 with e | ⟨t, t', ht, -, -, -⟩
    · exact agreeAt_of_not_tcb e hNot hx
    · rw [hx] at ht; cases ht; exact absurd rfl (hNot t)
  · exact agreeAt_of_not_tcb (h.2.1 x hc) hNot hx

/-- Every thread stays a thread. -/
theorem getTcb?_isSome (h : answerGuardFrame c s' s) (p : SeLe4n.ThreadId)
    (hp : (s.getTcb? p).isSome = true) : (s'.getTcb? p).isSome = true := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
  have h1 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
  by_cases hc : p.toObjId = c.toObjId
  · rcases h.2.2 with e | ⟨t0, t', -, ht', -, -⟩
    · obtain ⟨t', h', -⟩ := agreeAt_tcb (hc ▸ e) h1
      exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
    · exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr
        (hc ▸ ht')⟩
  · obtain ⟨t', h', -⟩ := agreeAt_tcb (h.2.1 _ hc) h1
    exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩

/-- The stash test reads the same. -/
theorem stasherTestAt (h : answerGuardFrame c s' s) (x : SeLe4n.ThreadId) (n : Nat) :
    _root_.SeLe4n.Kernel.stasherTestAt s' x n = _root_.SeLe4n.Kernel.stasherTestAt s x n := by
  by_cases hc : x.toObjId = c.toObjId
  · rcases h.2.2 with e | ⟨t, t', ht, ht', e1, e2⟩
    · exact stasherTestAt_of_view (hc ▸ e) n
    · unfold _root_.SeLe4n.Kernel.stasherTestAt SystemState.getTcb?
      rw [hc, ht, ht']
      simp only [e1, e2]
  · exact stasherTestAt_of_view (h.2.1 _ hc) n

end answerGuardFrame

/-- **The receive leg's guard carries across the caller's answer**: the
endpoint, the receiver (not the caller) and its admission, and
`receiveBlocksInPlace`, read before the answer, hold after it. -/
theorem receiveGuard_of_answerGuardFrame {c : SeLe4n.ThreadId} {s' s : SystemState}
    (h : answerGuardFrame c s' s)
    {epId : SeLe4n.ObjId} {ep : Endpoint} {tid : SeLe4n.ThreadId} {rt : TCB}
    {tail? : Option SeLe4n.ThreadId} {rid? : Option SeLe4n.ReplyId} (hNe : tid ≠ c)
    (hE : s.objects[epId]? = some (.endpoint ep))
    (hR : s.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hG : receiveBlocksInPlace s epId tid tail? rid? = true) :
    s'.objects[epId]? = some (.endpoint ep) ∧
      (∃ rt', s'.objects[tid.toObjId]? = some (.tcb rt') ∧ receiveBlockAdmits rt' = true ∧
        rt'.boundNotificationCode = rt.boundNotificationCode) ∧
      receiveBlocksInPlace s' epId tid tail? rid? = true := by
  have hTc : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  refine ⟨h.obj (fun _ e => by cases e) hE, ?_, ?_⟩
  · obtain ⟨rt', h1, e⟩ := agreeAt_tcb (h.2.1 _ hTc) hR
    refine ⟨rt', h1, ?_, ?_⟩
    · have : receiveBlockAdmits rt' = receiveBlockAdmits rt'.withoutRunLinks := rfl
      rw [this, e]; exact hA
    · show rt'.withoutRunLinks.boundNotificationCode = rt.withoutRunLinks.boundNotificationCode
      rw [e]
  · unfold receiveBlocksInPlace at hG ⊢
    simp only [Bool.and_eq_true] at hG ⊢
    obtain ⟨⟨hEnq, hSt⟩, hRec⟩ := hG
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ h.1 h.getObjectType? h.getTcb?_isSome hEnq, ?_⟩, ?_⟩
    · revert hSt
      cases rid? with
      | none => intro _; rfl
      | some rid =>
        simp only [SystemState.replyStashValid]
        cases hr : s.getReply? rid with
        | none => intro e; cases e
        | some r =>
          intro hs
          have h1 := h.obj (fun _ e => by cases e) ((SystemState.getReply?_eq_some_iff _ _ _).mp hr)
          rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr h1]
          dsimp only at hs ⊢
          rw [replyStashedAt_eq_stasherTestAt] at hs ⊢
          revert hs
          cases r.stasherCode with
          | zero => exact id
          | succ k => dsimp only; rw [h.stasherTestAt]; exact id
    · revert hRec
      cases rid? with
      | none => exact id
      | some rid =>
        simp only [SeLe4n.ReplyId.optCode, replyRecordsInPlace, Bool.and_eq_true]
        rintro ⟨a, b⟩
        exact ⟨(h.1 _).trans a, storeLeavesIndexAndTypes_of_frame h.getObjectType? b⟩

/-! ## The per-arm reply legs, blocking

Each reply arm's guard, the receive guard its leg carries, and its leg's
equality to the specification, which `replyRecvAnsweringOnCore_arm_inPlace`
cases over. -/

/-- The state after a reply leg whose caller is `c` and whose reply object is
`rid`, holding message `msg`: the facts the receive leg's guard reads, carried
over from the pre-state. -/
theorem storeReplyRendezvous_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hFree : rp.consumed.isFree = true) (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (storeReplyRendezvous st c tid rid msg).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt1, (storeReplyRendezvous st c tid rid msg).objects[tid.toObjId]? = some (.tcb rt1) ∧
        receiveBlockAdmits rt1 = true ∧ rt1.boundNotificationCode = rt.boundNotificationCode) ∧
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
    refine ⟨rt1, by rw [hHold _ hTc']; exact h1, ?_, ?_⟩
    · have : receiveBlockAdmits rt1 = receiveBlockAdmits rt1.withoutRunLinks := rfl
      rw [this, e1]; exact hA
    · show rt1.withoutRunLinks.boundNotificationCode = rt.withoutRunLinks.boundNotificationCode
      rw [e1]
  · unfold receiveBlocksInPlace
    rw [Bool.and_eq_true, Bool.and_eq_true]
    have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
    obtain ⟨tc1, htc1, hc1⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
    have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
      hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
    -- every key: the caller and its reply object by name, the rest by agreement
    have hAt : ∀ x, (x = c.toObjId ∧
          ∃ t, (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.tcb t) ∧
            t.ipcStateCode = (receiverReady ct).ipcStateCode) ∨
        (x = rid.toObjId ∧
          (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.reply rp.consumed)) ∨
        ((S1.mapTcbInPlace c (holdMessage msg)).objects[x]?).map KernelObject.withoutRunLinks =
          (st.objects[x]?).map KernelObject.withoutRunLinks := by
      intro x
      by_cases hxc : x = c.toObjId
      · subst hxc
        left
        refine ⟨rfl, holdMessage msg tc1, ?_, hc1⟩
        rw [SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
      · by_cases hxr : x = rid.toObjId
        · subst hxr; right; left; rw [hHold _ hxc]; exact ⟨rfl, hR1⟩
        · right; right; rw [hHold _ hxc]; exact hAg x hxc hxr
    have hV : ∀ x, (S1.mapTcbInPlace c (holdMessage msg)).getObjectType? x =
        st.getObjectType? x := by
      intro x
      rcases hAt x with ⟨e, t, h, _⟩ | ⟨e, h⟩ | h
      · subst e; unfold SystemState.getObjectType?; rw [h, hT]; rfl
      · subst e; unfold SystemState.getObjectType?; rw [h, hRp]; rfl
      · exact getObjectType?_of_view h
    have hKF : (S1.mapTcbInPlace c (holdMessage msg)).objectsKeepFinds st :=
      (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ hKF hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
      have h1 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
      rcases hAt p.toObjId with ⟨_, t', h, _⟩ | ⟨e, _⟩ | h
      · exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h⟩
      · rw [e, hRp] at h1; cases h1
      · obtain ⟨t', h', _⟩ := agreeAt_tcb h h1
        exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
    · -- The Reply records the thread that stashes it; that thread is the
      -- caller (now ready), the Reply's own key (no thread) or a thread the
      -- reply leg leaves as it was off its run-queue links.
      have hSt : (S1.mapTcbInPlace c (holdMessage msg)).replyStashedAt rid rp.consumed = false := by
        rw [replyStashedAt_eq_stasherTestAt, Reply.consumed_stasherCode]
        rw [replyStashedAt_eq_stasherTestAt] at hStash
        revert hStash
        cases rp.stasherCode with
        | zero => intro _; rfl
        | succ k =>
          intro hStash
          dsimp only at hStash ⊢
          rcases hAt (⟨k⟩ : SeLe4n.ThreadId).toObjId with ⟨_, t, h, hc⟩ | ⟨_, h⟩ | h
          · unfold stasherTestAt SystemState.getTcb?; rw [h]
            simp only [hc, receiverReady, TCB.setIpcState_ipcStateCode]
            rfl
          · unfold stasherTestAt SystemState.getTcb?; rw [h]
          · rw [stasherTestAt_of_view h]; exact hStash
      simp only [SystemState.replyStashValid]
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr (by rw [hHold _ hRc]; exact hR1)]
      simp only [hSt, hFree]
      rfl
    · show replyRecordsInPlace _ (rid.val + 1) = true
      simp only [replyRecordsInPlace, Bool.and_eq_true] at hRec ⊢
      exact ⟨(hKF _).trans hRec.1, storeLeavesIndexAndTypes_of_frame
        (s' := S1.mapTcbInPlace c (holdMessage msg)) hV hRec.2⟩

/-- The state the receive leg runs on, in the order the fast forms take: a
faulted caller's answer first, as the composite now runs it (WS-SX SX32, seL4's
`doReplyTransfer` before `handleRecv`); an ordinary answer stages a register
frame, which the fast forms write last (`replyRecvStageLast`), the two orders
being equal there (`endpointReplyRecvAnsweringOnCore_answerFirst_at`). -/
@[inline] def replyRecvFaultFirst (answer : Option Architecture.FaultReplyOutcome) (Y : SystemState)
    (c : SeLe4n.ThreadId) : SystemState :=
  match answer with
  | none => Y
  | some f => faultReplyApplyOnCore Y c f

/-- What is left of the caller's answer once the receive leg has run: the
ordinary answer's frame staged, reporting `capInfo`; nothing for a fault, answered first
(`replyRecvFaultFirst`). -/
@[inline] def replyRecvStageLast (answer : Option Architecture.FaultReplyOutcome) (Z : SystemState)
    (c : SeLe4n.ThreadId) (capInfo : Nat) : SystemState :=
  match answer with
  | none => Architecture.stageDeliveredMessage Z c capInfo
  | some _ => Z

/-- **The receive's guard on the state it runs on**: read on the state the
reply leg and the pop leave, it holds on that state with a fault answered first. -/
theorem replyRecvFaultFirst_receiveGuard (answer : Option Architecture.FaultReplyOutcome)
    {P : SystemState} {c tid : SeLe4n.ThreadId} {epId : SeLe4n.ObjId} {ep : Endpoint} {rt : TCB}
    {tail? : Option SeLe4n.ThreadId} {rid? : Option SeLe4n.ReplyId} (hNe : tid ≠ c)
    (hNo : P.objects.noResizeDue)
    (hE : P.objects[epId]? = some (.endpoint ep))
    (hR : P.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hG : receiveBlocksInPlace P epId tid tail? rid? = true) :
    (replyRecvFaultFirst answer P c).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt', (replyRecvFaultFirst answer P c).objects[tid.toObjId]? = some (.tcb rt') ∧
        receiveBlockAdmits rt' = true) ∧
      receiveBlocksInPlace (replyRecvFaultFirst answer P c) epId tid tail? rid? = true ∧
      (replyRecvFaultFirst answer P c).objects.noResizeDue := by
  cases answer with
  | none => exact ⟨hE, ⟨rt, hR, hA⟩, hG, hNo⟩
  | some f =>
    obtain ⟨hF, hNoA⟩ := faultReplyApplyOnCore_answerGuardFrame P c f hNo
    obtain ⟨a, ⟨r, b, d, -⟩, e⟩ := receiveGuard_of_answerGuardFrame hF hNe hE hR hA hG
    exact ⟨a, ⟨r, b, d⟩, e, hNoA⟩

/-- **The reply-receive that blocks, in place, on either answer**: under the reply's guard
(`replyWakesInPlace`), with the receiver the server the caller recorded, no
sender waiting and the receive's block admissible (read on the pre-state and
carried across the reply leg, `storeReplyRendezvous_receiveGuard`, and across a
fault answer, `receiveGuard_of_answerGuardFrame`), the composite answering the
caller with `answer` is the reply's writes, a fault's answer, the receive's
block, the server's priority walk and an ordinary answer's frame staged. -/
theorem replyRecvAnsweringOnCore_blocks_inPlace
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hFree : rp.consumed.isFree = true) (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : answer = none →
      replyTransferInert st tid ct grant = true) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvStageLast answer
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true
              (replyRecvFaultFirst answer (storeReplyRendezvous st c tid rid msg) c) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  obtain ⟨hE0, ⟨rt0, hR0, hA0, -⟩, hG0⟩ := storeReplyRendezvous_receiveGuard st c tid rid msg ct rp
    epId ep rt hNo hT hFC hRp hNe hE hR hA hEnq hFree hStash hRec
  have hNo1 := storeReplyRendezvous_noResizeDue st c tid rid msg hNo
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  cases answer with
  | none =>
    have hXf := replyRecvReplyTransfer_of_inert none st tid c grant ct hTc hInert
      (storeReplyRendezvous st c tid rid msg)
    have h := replyRecvOnCore_blocks_transfer st epId tid c rid msg grant core ct ep0 ep hSz hT hIpc
      hRO hG hS hXf hE0 hR0 hA0 hNo1 hG0 hNe
    simpa only [CapTransferSummary.capInfo_empty] using h
  | some f =>
  obtain ⟨hEq, hHead⟩ := replyOnCore_inPlace st tid c tid ct ep0 rid msg core hSz
    hT hIpc hRO hG
  obtain ⟨hF, hNoA⟩ := faultReplyApplyOnCore_answerGuardFrame (storeReplyRendezvous st c tid rid msg)
    c f hNo1
  obtain ⟨hE0', ⟨rt0', hR0', hA0', -⟩, hG0'⟩ := receiveGuard_of_answerGuardFrame hF hNe hE0 hR0 hA0
    hG0
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := receiveReturnSchedContext_receiveGuard true _ tid hNoA
    hE0' hR0' hA0' hG0'
  have hRec : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  simp only [replyRecvStageLast, replyRecvFaultFirst]
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hHead hE1 hR1 hG1
  generalize hA1' : faultReplyApplyOnCore S1 c f = A at hE1 hR1 hG1
  have hPop : replyRecvPopDonation rid c S1 = .ok (none, S1) := by
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
  have hEp1 : (receiveReturnSchedContext true A tid).getEndpoint? epId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE1
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core
      (receiveReturnSchedContext true A tid) =
      (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true A tid) epId tid
        ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq _ epId ep tid rt1 (some rid) core hE1 hS hR1 hA1 hG1]
    have hSnd : (receiveRendezvousSender? (receiveReturnSchedContext true A tid) epId).isNone =
        true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  have hRes : tid.isReserved = false := by
    have h := hG1
    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1
  unfold endpointReplyRecvAnsweringOnCore
  simp only [hRec, Option.getD_some, hEq, hPop, replyRecvReplyTransfer, replyRecvAnswerCaller, hA1',
    hRecv, Option.bind_some, hS, replyRecvPostReceiveDonation_none_self _ _ _ _ hRes]
  simp [applyReceiveLegPipHandoff]

/-- **A donated reply-receive that may block in place**, read on the
pre-state: the caller blocked on a reply from the receiver through reply object
`rid`, the pop's checks (`replyPopsInPlace`), no sender waiting on the
endpoint, the receiver an unreserved thread that may block there in place once
the pop unbinds it, and its reply object not stashed and in its slot for the
stasher record.  Every read is a code. -/
@[inline] def replyRecvDonatedBlocks (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyPopsInPlace st c ct.scBindingScCode tid rid
   | none => false) &&
  !tid.isReserved &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => enqueueAdmits rt && enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => !st.replyStashedAt rid rp && replyRecordsInPlace st (rid.val + 1)
   | none => false)

theorem replyRecvDonatedBlocks_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvDonatedBlocks st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 (some tid) ∧ ct.replyObject = some rid ∧
      replyPopsInPlace st c ct.scBindingScCode tid rid = true ∧ tid.isReserved = false ∧
      st.objects[epId]? = some (.endpoint ep) ∧ ep.sendQ.head = none ∧
      st.objects[tid.toObjId]? = some (.tcb rt) ∧ enqueueAdmits rt = true ∧
      enqueuesInPlace st epId tid ep.receiveQ.tail = true ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.replyStashedAt rid rp = false ∧ replyRecordsInPlace st (rid.val + 1) = true := by
  unfold replyRecvDonatedBlocks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hC, hSRes⟩, hE⟩, hRp⟩ := h
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hIpc, hRO⟩, hW⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid) := by
    revert hIpc
    split
    · next ep0 server hS =>
      intro e
      have : server = tid := by
        cases server; cases tid; simp only [beq_iff_eq] at e; subst e; rfl
      subst this
      exact ⟨ep0, hS⟩
    · intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨hA, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨hStash, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hSRes, (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, hStash, hRecR⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq

/-- **The donation pop carries the receive's guard**: on the state a donated
reply leg and its pop leave, the endpoint is as it was, the server (unbound by
the pop) may block on it and its block writes in place, each read on the
pre-state. -/
theorem popDonationSettled_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (home : CoreId)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId home).objects[epId]? =
        some (.endpoint ep) ∧
      (∃ rt1, (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
          home).objects[tid.toObjId]? = some (.tcb rt1) ∧ receiveBlockAdmits rt1 = true ∧
          rt1.boundNotificationCode = rt.boundNotificationCode) ∧
      receiveBlocksInPlace (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
        scId home) epId tid ep.receiveQ.tail (some rid) = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  have hSc' : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hSr : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
  obtain ⟨tc1, htc1, hc1⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T
  have hNoT : T.objects.noResizeDue := by rw [← hTdef]; exact hNo1
  have hHold : ∀ x, x ≠ c.toObjId → T.objects[x]? = S1.objects[x]? := fun x hx => by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hTC : T.objects[c.toObjId]? = some (.tcb (holdMessage msg tc1)) := by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [hHold _ hx]; exact hAg x hx hy
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by rw [hHold _ hRc]; exact hR1
  have hKT : T.objectsKeepFinds st := by
    rw [← hTdef]; exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  -- the pop's reads on `T`
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hSc' hSr) (fun _ e => by cases e) hScO)
  obtain ⟨rtT, hRtT, _⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  obtain ⟨⟨t, hPt, hB0⟩, hPr⟩ := returnDonatedSchedContextInPlace_exact T tid c scId sc rid rp.consumed
    (holdMessage msg tc1) rtT hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC) ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRtT)
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hFr := returnDonatedSchedContextInPlace_popFrame T tid c scId hNoT
  unfold popDonationSettledInPlace
  generalize returnDonatedSchedContextInPlace T tid c scId = Rr at hPt hPr hFr
  have hAgS := SchedContextOps.settleReturnedContext_agree Rr home scId
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  generalize SchedContextOps.settleReturnedContext Rr home scId = P at hAgS hF
  have hPt' : P.objects[tid.toObjId]? = some (.tcb t) :=
    releaseAgreeAt_of_not_sc hAgS hPt (fun _ e => by cases e)
  have hPr' : P.objects[rid.toObjId]? =
      some (.reply { rp.consumed with prev := none, next := none }) :=
    releaseAgreeAt_of_not_sc hAgS hPr (fun _ e => by cases e)
  have hComb : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (P.objects[x]?).map popFieldsView = (st.objects[x]?).map popFieldsView :=
    fun x hx hy => (hF.2.2.2 x).trans (popAgreeAt_of_runLinks (hView x hx hy))
  obtain ⟨tcP, hPC, ecP⟩ := popAgreeAt_tcb (hF.2.2.2 c.toObjId) hTC
  refine ⟨popAgreeAt_endpoint (hComb _ hEc hEr) hE, ⟨t, hPt', ?_, ?_⟩, ?_⟩
  · obtain ⟨t', h', e'⟩ := popAgreeAt_tcb (hComb _ hTc' hTr) hR
    rw [hPt'] at h'
    cases h'
    unfold receiveBlockAdmits
    rw [← enqueueAdmits_popView t, e', enqueueAdmits_popView, hA]
    have hU : t.schedContextBinding = .unbound := by
      unfold TCB.schedContextBinding SchedContextBinding.ofCodes; rw [hB0]
    rw [hU]
    rfl
  · obtain ⟨t', h', e'⟩ := popAgreeAt_tcb (hComb _ hTc' hTr) hR
    rw [hPt'] at h'
    cases h'
    have := congrArg TCB.boundNotificationCode e'
    exact this
  · unfold receiveBlocksInPlace
    have hKP : P.objectsKeepFinds st := hF.2.2.1.trans hKT
    have hV : ∀ x, P.getObjectType? x = st.getObjectType? x := by
      intro x
      by_cases hxc : x = c.toObjId
      · subst hxc; unfold SystemState.getObjectType?
        rw [hPC, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
      · by_cases hxr : x = rid.toObjId
        · subst hxr; unfold SystemState.getObjectType?; rw [hPr', hRp]; rfl
        · exact getObjectType?_of_popAgree (hComb x hxc hxr)
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ hKP hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      by_cases hpc : p.toObjId = c.toObjId
      · exact Option.isSome_iff_exists.mpr
          ⟨tcP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ hPC)⟩
      · by_cases hpr : p.toObjId = rid.toObjId
        · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
          have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
          rw [hpr, hRp] at this; cases this
        · exact getTcb?_isSome_of_popAgree (hComb _ hpc hpr) hp
    · have hFree : ({ rp.consumed with prev := none, next := none } : Reply).isFree = true := by
        have h := Reply.consumed_caller rp
        simp only [Reply.caller] at h
        simp only [Reply.isFree, Reply.caller, h, Option.isNone_none, Bool.and_self]
      have hSt : P.replyStashedAt rid { rp.consumed with prev := none, next := none } = false := by
        rw [replyStashedAt_eq_stasherTestAt]
        rw [replyStashedAt_eq_stasherTestAt] at hStash
        show (match rp.consumed.stasherCode with
          | 0 => false
          | k + 1 => stasherTestAt P (⟨k⟩ : SeLe4n.ThreadId) (rid.val + 1)) = false
        rw [Reply.consumed_stasherCode]
        revert hStash
        cases rp.stasherCode with
        | zero => intro _; rfl
        | succ k =>
          intro hStash
          dsimp only at hStash ⊢
          by_cases hkc : (⟨k⟩ : SeLe4n.ThreadId).toObjId = c.toObjId
          · unfold stasherTestAt SystemState.getTcb?
            rw [hkc, hPC]
            have e := congrArg TCB.ipcStateCode ecP
            simp only [TCB.withoutRunLinks] at e
            simp only [e]
            show ((holdMessage msg tc1).ipcStateCode == 1 && _) = false
            have e2 : (holdMessage msg tc1).ipcStateCode = tc1.ipcStateCode := rfl
            simp only [e2, hc1, receiverReady, TCB.setIpcState_ipcStateCode]
            rfl
          · by_cases hkr : (⟨k⟩ : SeLe4n.ThreadId).toObjId = rid.toObjId
            · unfold stasherTestAt SystemState.getTcb?; rw [hkr, hPr']
            · rw [stasherTestAt_of_popAgree (hComb _ hkc hkr)]; exact hStash
      simp only [SystemState.replyStashValid]
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hPr']
      simp only [hSt, hFree]
      rfl
    · show replyRecordsInPlace _ (rid.val + 1) = true
      simp only [replyRecordsInPlace, Bool.and_eq_true] at hRec ⊢
      exact ⟨(hKP _).trans hRec.1, storeLeavesIndexAndTypes_of_frame hV hRec.2⟩

/-- **The donated reply-receive that blocks, in place**: under the pop's guard
(`replyPopsInPlace`) with the receiver the server the caller recorded, no sender
waiting and the receive's block admissible once the pop unbinds the server, each
read on the pre-state and carried across the reply leg and the pop
(`popDonationSettled_receiveGuard`), the specification's reply-receive is the
reply's writes, the pop and its settle, the receive's block, the server taken
off its core, its priority walk and the caller's staged message. -/
theorem replyRecvAnsweringOnCore_donated_inPlace
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : answer = none →
      replyTransferInert st tid ct grant = true) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvStageLast answer
        (PriorityInheritance.propagatePipChainCrossCore
          (descheduleAtPlacement (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true (replyRecvFaultFirst answer
              (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
                ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c)) c) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true (replyRecvFaultFirst answer
              (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid
                ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c)) c) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId := by
  obtain ⟨rp', scId, sc, hRp', hN, hScO, hHead, hBelow, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR,
    _, hPop⟩ := replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
  rw [hRp] at hRp'
  cases hRp'
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  obtain ⟨hE1, ⟨rt1, hR1, hA1, hB1⟩, hG1⟩ := popDonationSettled_receiveGuard st c tid rid msg ct rp
    epId ep rt scId sc (determineTargetCore st c) hNo hT hFC hRp hN hScO hHead hBelow
    (fun e => hNe e.symm) hE hR hA hEnq hStash hRec
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hXf := replyRecvReplyTransfer_of_inert answer st tid c grant ct hTc hInert
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hNoP := popDonationSettledInPlace_noResizeDue _ c tid scId (determineTargetCore st c)
    (storeReplyRendezvous_noResizeDue st c tid rid msg hNo)
  cases answer with
  | none =>
    obtain ⟨hE2, ⟨rt2, hR2, hA2⟩, hG2⟩ := receiveReturnSchedContext_receiveGuard true _ tid hNoP
      hE1 hR1 hA1 hG1
    refine ⟨?_, receiveBlock_receiver_blocked _ epId ep tid rt2 (some rid) core hE2 hR2 hA2 hG2⟩
    have h := replyRecvOnCore_donated_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT
      hIpc hRO hSRes hG hS hRp
      (S2 := popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid scId
        (determineTargetCore st c))
      (by rw [hSc]; exact replyRecvReplyTransfer_of_inert none st tid c grant ct hTc hInert _)
      hE1 hR1 hA1 hNoP hG1 (fun e => hNe e.symm)
    simpa only [CapTransferSummary.capInfo_empty] using h
  | some f =>
  obtain ⟨hF, hNoA⟩ := faultReplyApplyOnCore_answerGuardFrame _ c f hNoP
  obtain ⟨hE1, ⟨rt1, hR1, hA1, -⟩, hG1⟩ := receiveGuard_of_answerGuardFrame hF (fun e => hNe e.symm)
    hE1 hR1 hA1 hG1
  simp only [replyRecvStageLast, replyRecvFaultFirst]
  rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hPop hE1 hR1 hG1 hNoA
  generalize hP : popDonationSettledInPlace S1 c tid scId (determineTargetCore st c) = P
    at hPop hE1 hR1 hG1 hNoA
  generalize hAP : faultReplyApplyOnCore P c f = A at hE1 hR1 hG1 hNoA
  obtain ⟨hE2, ⟨rt2, hR2, hA2⟩, hG2⟩ := receiveReturnSchedContext_receiveGuard true A tid hNoA
    hE1 hR1 hA1 hG1
  generalize hQ : receiveReturnSchedContext true A tid = Q at hE2 hR2 hG2
  have hEp1 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt2 (some rid) core hE2 hS hR2 hA2 hG2]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked Q epId ep tid rt2 (some rid) core hE2 hR2
    hA2 hG2
  have hDq : rendezvousDequeuedCall (removeRunnableOnCore (storeReceiveBlock Q epId tid
      ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid = false := by
    unfold rendezvousDequeuedCall lookupTcb
    simp only [hSRes, Bool.false_eq_true, ↓reduceIte, hTb, hBk]
  refine ⟨?_, tb, hTb, hBk⟩
  unfold endpointReplyRecvAnsweringOnCore
  simp only [hRecS, Option.getD_some, hEq, hPop, replyRecvReplyTransfer, replyRecvAnswerCaller, hAP,
    hQ, hRecv, hEp1, Option.bind_some, hS]
  simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff]

/-- Whether reply object `rid` has no frame below it on its context's stack, so
a pop of it leaves the context with no loan owed. -/
@[inline] def replyIsStackBottom (st : SystemState) (rid : SeLe4n.ReplyId) : Bool :=
  match st.getReply? rid with
  | some rp => rp.prev.isNone
  | none => false

/-- **A held reply-receive that may block in place**, read on the pre-state:
the caller blocked on a reply from the receiver through reply object `rid`, the
held pop's checks (`replyHeldPopsInPlace`), no sender waiting on the endpoint,
the receiver an unreserved thread the held pop leaves `.bound` (it owns the
context it holds, or the popped frame is the stack's last, so the context it
keeps is its own) and whose block writes in place, and its reply object not
stashed and in its slot for the stasher record.  Every read is a code. -/
@[inline] def replyRecvHeldBlocks (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyHeldPopsInPlace st c ct.scBindingScCode tid rid
   | none => false) &&
  !tid.isReserved &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => (rt.scBindingOwnerCode == 0 || replyIsStackBottom st rid) &&
            enqueueAdmits rt && enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => !st.replyStashedAt rid rp && replyRecordsInPlace st (rid.val + 1)
   | none => false)

theorem replyRecvHeldBlocks_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvHeldBlocks st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 (some tid) ∧ ct.replyObject = some rid ∧
      replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true ∧ tid.isReserved = false ∧
      st.objects[epId]? = some (.endpoint ep) ∧ ep.sendQ.head = none ∧
      st.objects[tid.toObjId]? = some (.tcb rt) ∧
      (rt.scBindingOwnerCode = 0 ∨ rp.prev = none) ∧ enqueueAdmits rt = true ∧
      enqueuesInPlace st epId tid ep.receiveQ.tail = true ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.replyStashedAt rid rp = false ∧ replyRecordsInPlace st (rid.val + 1) = true := by
  unfold replyRecvHeldBlocks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hC, hSRes⟩, hE⟩, hRp⟩ := h
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hIpc, hRO⟩, hW⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid) := by
    revert hIpc
    split
    · next ep0 server hS =>
      intro e
      have : server = tid := by
        cases server; cases tid; simp only [beq_iff_eq] at e; subst e; rfl
      subst this
      exact ⟨ep0, hS⟩
    · intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨hOwn, hA⟩, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨hStash, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hSRes, (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, ?_, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, hStash, hRecR⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · simp only [Bool.or_eq_true, beq_iff_eq, replyIsStackBottom, hR,
      Option.isNone_iff_eq_none] at hOwn
    exact hOwn
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq

/-- **The held pop carries the receive's guard**: on the state a held reply
leg and its pop leave, the endpoint is as it was, the server (still `.bound` to
the context it owns) may block on it and its block writes in place, each read
on the pre-state. -/
theorem keepHeldPop_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hOwn : rt.scBindingOwnerCode = 0 ∨ rp.prev = none)
    (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid scId).objects[epId]? =
        some (.endpoint ep) ∧
      (∃ rt1, (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid scId).objects[tid.toObjId]? = some (.tcb rt1) ∧ receiveBlockAdmits rt1 = true ∧
          rt1.boundNotificationCode = rt.boundNotificationCode) ∧
      receiveBlocksInPlace (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg)
        tid scId) epId tid ep.receiveQ.tail (some rid) = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  have hSc' : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hSr : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
  obtain ⟨tc1, htc1, hc1⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T
  have hNoT : T.objects.noResizeDue := by rw [← hTdef]; exact hNo1
  have hHold : ∀ x, x ≠ c.toObjId → T.objects[x]? = S1.objects[x]? := fun x hx => by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hTC : T.objects[c.toObjId]? = some (.tcb (holdMessage msg tc1)) := by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [hHold _ hx]; exact hAg x hx hy
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by rw [hHold _ hRc]; exact hR1
  have hKT : T.objectsKeepFinds st := by
    rw [← hTdef]; exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  -- the pop's reads on `T`
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hSc' hSr) (fun _ e => by cases e) hScO)
  obtain ⟨rtT, hRtT, eRtT⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  obtain ⟨⟨t, hPt', hB0, hB1, _⟩, hPr'⟩ := keepDonatedSchedContextInPlace_exact T tid scId sc rid
    rp.consumed rtT hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hRtT)
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hF := keepDonatedSchedContextInPlace_popFrame T tid scId hNoT
  have hOwnT : heldPopOwnerCode rtT.scBindingOwnerCode (popOuterCode T rp.consumed) = 0 := by
    rcases hOwn with h | h
    · have h' : rtT.scBindingOwnerCode = 0 := (congrArg TCB.scBindingOwnerCode eRtT).trans h
      rw [h']; rfl
    · rw [hHeadC]; simp only [popOuterCode, h]; unfold heldPopOwnerCode; split <;> rfl
  rw [hOwnT] at hB1
  generalize keepDonatedSchedContextInPlace T tid scId = P at hPt' hPr' hF
  have hComb : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (P.objects[x]?).map popFieldsView = (st.objects[x]?).map popFieldsView :=
    fun x hx hy => (hF.2.2.2 x).trans (popAgreeAt_of_runLinks (hView x hx hy))
  obtain ⟨tcP, hPC, ecP⟩ := popAgreeAt_tcb (hF.2.2.2 c.toObjId) hTC
  refine ⟨popAgreeAt_endpoint (hComb _ hEc hEr) hE, ⟨t, hPt', ?_, ?_⟩, ?_⟩
  · obtain ⟨t', h', e'⟩ := popAgreeAt_tcb (hComb _ hTc' hTr) hR
    rw [hPt'] at h'
    cases h'
    unfold receiveBlockAdmits
    rw [← enqueueAdmits_popView t, e', enqueueAdmits_popView, hA]
    have hU : t.schedContextBinding = .bound scId := by
      unfold TCB.schedContextBinding SchedContextBinding.ofCodes
      rw [hB0, hB1]
    rw [hU]
    rfl
  · obtain ⟨t', h', e'⟩ := popAgreeAt_tcb (hComb _ hTc' hTr) hR
    rw [hPt'] at h'
    cases h'
    have := congrArg TCB.boundNotificationCode e'
    exact this
  · unfold receiveBlocksInPlace
    have hKP : P.objectsKeepFinds st := hF.2.2.1.trans hKT
    have hV : ∀ x, P.getObjectType? x = st.getObjectType? x := by
      intro x
      by_cases hxc : x = c.toObjId
      · subst hxc; unfold SystemState.getObjectType?
        rw [hPC, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
      · by_cases hxr : x = rid.toObjId
        · subst hxr; unfold SystemState.getObjectType?; rw [hPr', hRp]; rfl
        · exact getObjectType?_of_popAgree (hComb x hxc hxr)
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ hKP hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      by_cases hpc : p.toObjId = c.toObjId
      · exact Option.isSome_iff_exists.mpr
          ⟨tcP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ hPC)⟩
      · by_cases hpr : p.toObjId = rid.toObjId
        · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
          have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
          rw [hpr, hRp] at this; cases this
        · exact getTcb?_isSome_of_popAgree (hComb _ hpc hpr) hp
    · have hFree : ({ rp.consumed with prev := none, next := none } : Reply).isFree = true := by
        have h := Reply.consumed_caller rp
        simp only [Reply.caller] at h
        simp only [Reply.isFree, Reply.caller, h, Option.isNone_none, Bool.and_self]
      have hSt : P.replyStashedAt rid { rp.consumed with prev := none, next := none } = false := by
        rw [replyStashedAt_eq_stasherTestAt]
        rw [replyStashedAt_eq_stasherTestAt] at hStash
        show (match rp.consumed.stasherCode with
          | 0 => false
          | k + 1 => stasherTestAt P (⟨k⟩ : SeLe4n.ThreadId) (rid.val + 1)) = false
        rw [Reply.consumed_stasherCode]
        revert hStash
        cases rp.stasherCode with
        | zero => intro _; rfl
        | succ k =>
          intro hStash
          dsimp only at hStash ⊢
          by_cases hkc : (⟨k⟩ : SeLe4n.ThreadId).toObjId = c.toObjId
          · unfold stasherTestAt SystemState.getTcb?
            rw [hkc, hPC]
            have e := congrArg TCB.ipcStateCode ecP
            simp only [TCB.withoutRunLinks] at e
            simp only [e]
            show ((holdMessage msg tc1).ipcStateCode == 1 && _) = false
            have e2 : (holdMessage msg tc1).ipcStateCode = tc1.ipcStateCode := rfl
            simp only [e2, hc1, receiverReady, TCB.setIpcState_ipcStateCode]
            rfl
          · by_cases hkr : (⟨k⟩ : SeLe4n.ThreadId).toObjId = rid.toObjId
            · unfold stasherTestAt SystemState.getTcb?; rw [hkr, hPr']
            · rw [stasherTestAt_of_popAgree (hComb _ hkc hkr)]; exact hStash
      simp only [SystemState.replyStashValid]
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hPr']
      simp only [hSt, hFree]
      rfl
    · show replyRecordsInPlace _ (rid.val + 1) = true
      simp only [replyRecordsInPlace, Bool.and_eq_true] at hRec ⊢
      exact ⟨(hKP _).trans hRec.1, storeLeavesIndexAndTypes_of_frame hV hRec.2⟩

theorem replyRecvAnsweringOnCore_held_inPlace
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hOwn : rt.scBindingOwnerCode = 0 ∨ rp.prev = none)
    (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : answer = none →
      replyTransferInert st tid ct grant = true) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvStageLast answer
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true (replyRecvFaultFirst answer
              (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
                ⟨replyHeadContextCode st rid - 1⟩) c) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true (replyRecvFaultFirst answer
              (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
                ⟨replyHeadContextCode st rid - 1⟩) c) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId := by
  obtain ⟨rp', scId, sc, _, hRp', hN, hScO, hHead, hBelow, hCode, hCRes, _, hNe, hNo, _, _, hLC, hFC,
    hLR, hFR, _, hPop⟩ := replyHeldPopsInPlace_pop st c tid rid msg ct hT hG
  rw [hRp] at hRp'
  cases hRp'
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  obtain ⟨hE1, ⟨rt1, hR1, hA1, hB1⟩, hG1⟩ := keepHeldPop_receiveGuard st c tid rid msg ct rp
    epId ep rt scId sc hNo hT hFC hRp hN hScO hHead hBelow
    (fun e => hNe e.symm) hE hR hOwn hA hEnq hStash hRec
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hXf := replyRecvReplyTransfer_of_inert answer st tid c grant ct hTc hInert
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hNoP := keepDonatedSchedContextInPlace_noResizeDue _ tid scId
    (storeReplyRendezvous_noResizeDue st c tid rid msg hNo)
  rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hPop hE1 hR1 hG1 hNoP
  generalize hP : keepDonatedSchedContextInPlace S1 tid scId = P
    at hPop hE1 hR1 hG1 hNoP
  -- the state the receive runs on: a fault answered first, an ordinary answer staged last
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1, hNoY⟩ : (replyRecvFaultFirst answer P c).objects[epId]? =
        some (.endpoint ep) ∧
      (∃ rt', (replyRecvFaultFirst answer P c).objects[tid.toObjId]? = some (.tcb rt') ∧
        receiveBlockAdmits rt' = true) ∧
      receiveBlocksInPlace (replyRecvFaultFirst answer P c) epId tid ep.receiveQ.tail (some rid) =
        true ∧ (replyRecvFaultFirst answer P c).objects.noResizeDue := by
    cases answer with
    | none => exact ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1, hNoP⟩
    | some f =>
      obtain ⟨hF, hNoA⟩ := faultReplyApplyOnCore_answerGuardFrame P c f hNoP
      obtain ⟨a, ⟨r, b, d, -⟩, e⟩ := receiveGuard_of_answerGuardFrame hF (fun e => hNe e.symm)
        hE1 hR1 hA1 hG1
      exact ⟨a, ⟨r, b, d⟩, e, hNoA⟩
  generalize hY : replyRecvFaultFirst answer P c = Y at hE1 hR1 hG1 hNoY
  obtain ⟨hE2, ⟨rt2, hR2, hA2⟩, hG2⟩ := receiveReturnSchedContext_receiveGuard true Y tid hNoY
    hE1 hR1 hA1 hG1
  generalize hQ : receiveReturnSchedContext true Y tid = Q at hE2 hR2 hG2
  have hEp1 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt2 (some rid) core hE2 hS hR2 hA2 hG2]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked Q epId ep tid rt2 (some rid) core hE2 hR2
    hA2 hG2
  have hDq : rendezvousDequeuedCall (removeRunnableOnCore (storeReceiveBlock Q epId tid
      ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid = false := by
    unfold rendezvousDequeuedCall lookupTcb
    simp only [hSRes, Bool.false_eq_true, ↓reduceIte, hTb, hBk]
  refine ⟨?_, tb, hTb, hBk⟩
  cases answer with
  | none =>
    have hNoQ : Q.objects.noResizeDue := hQ ▸ receiveReturnSchedContext_noResizeDue true Y tid hNoY
    have hSnd0 : receiveRendezvousSender? Q epId = none := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [replyRecvFaultFirst] at hY
    subst hY
    rw [endpointReplyRecvAnsweringOnCore_answerFirst_at none epId tid rid c msg grant core st
      (by simp) (Ne.symm (fun e => hNe e.symm)) hEq hPop (hXf P) hNoP (by rw [hQ, hSnd0]; simp)
      (fun _ => .inr ⟨by rw [hQ]; unfold receiveCapRequest; rw [hSnd0], fun s0 E hE => ?_⟩)]
    · simp only [hRecS, Option.getD_some, hQ, hRecv]
      simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff, replyRecvAnswerCaller,
        replyRecvStageLast]
    · simp only [hRecS, Option.getD_some, hQ, hRecv] at hE
      simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff] at hE
      obtain ⟨-, rfl⟩ := hE
      exact ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core
        (removeRunnableOnCore_noResizeDue _ _ _ (storeReceiveBlock_noResizeDue _ _ _ _ _ hNoQ))).trans
        ((ipcBufferReadsAgree_removeRunnableOnCore _ tid core).trans
          ((ipcBufferReadsAgree_storeReceiveBlock Q epId tid _ _ hNoQ).trans
            (hQ ▸ ipcBufferReadsAgree_receiveReturnSchedContext true _ tid hNoP)))).words
  | some f =>
    simp only [replyRecvFaultFirst] at hY
    unfold endpointReplyRecvAnsweringOnCore
    simp only [hRecS, Option.getD_some, hEq, hPop, hXf, replyRecvAnswerCaller, hY, hQ, hRecv,
      Option.bind_some, hS]
    simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff, replyRecvStageLast]

/-- **The unheld pop carries the receive's guard**: on the state the reply leg
to a caller recording no server and its unheld pop leave, the endpoint is as it
was, the replier may block on it and its block writes in place, each read on
the pre-state. -/
theorem popUnheldSettled_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) (home : CoreId)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp)) (hNext : rp.next = some (.head scId))
    (hScO : st.objects[scId.toObjId]? = some (.schedContext sc)) (hHead : sc.scReply = some rid)
    (hBelow : ∀ b, rp.prev = some b → b ≠ rid)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c scId) home scId).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt1, (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
          (storeReplyLeg st c rid msg) c scId) home scId).objects[tid.toObjId]? = some (.tcb rt1) ∧
        receiveBlockAdmits rt1 = true ∧ rt1.boundNotificationCode = rt.boundNotificationCode) ∧
      receiveBlocksInPlace (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c scId) home scId) epId tid ep.receiveQ.tail (some rid) =
        true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  have hSc' : scId.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hScO; cases hScO
  have hSr : scId.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hScO; cases hScO
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo]
  generalize hS1 : storeReplyLegReady st c rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyLegReady_agree st c rid ct hNo hTc hFC x hx hy
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ storeReplyLegReady_noResizeDue st c rid hNo
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyLegReady_keepsFinds st c rid hNo hFC
  obtain ⟨tc1, htc1, hcv⟩ := hS1 ▸ storeReplyLegReady_callerView st c rid ct hNo hTc hFC hRc
  have hc1 : tc1.ipcStateCode = (receiverReady ct).ipcStateCode := by
    have h := congrArg TCB.ipcStateCode hcv; exact h
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyLegReady_reply st c rid ct rp hNo hTc hFC hRp hRc
  generalize hTdef : S1.mapTcbInPlace c (holdMessage msg) = T
  have hNoT : T.objects.noResizeDue := by rw [← hTdef]; exact hNo1
  have hHold : ∀ x, x ≠ c.toObjId → T.objects[x]? = S1.objects[x]? := fun x hx => by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hTC : T.objects[c.toObjId]? = some (.tcb (holdMessage msg tc1)) := by
    rw [← hTdef, SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
  have hView : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (T.objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := fun x hx hy => by
    rw [hHold _ hx]; exact hAg x hx hy
  have hTR : T.objects[rid.toObjId]? = some (.reply rp.consumed) := by rw [hHold _ hRc]; exact hR1
  have hKT : T.objectsKeepFinds st := by
    rw [← hTdef]; exact (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  -- the pop's reads on `T`
  have hScT : T.getSchedContext? scId = some sc := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
    (agreeAt_of_not_tcb (hView _ hSc' hSr) (fun _ e => by cases e) hScO)
  obtain ⟨rtT, hRtT, eT⟩ := agreeAt_tcb (hView _ hTc' hTr) hR
  have hHeadC : rp.consumed = { rp with callerCode := 0 } := Reply.consumed_of_head rp scId hNext
  have hPr := returnUnheldSchedContextInPlace_reply T c scId sc rid rp.consumed (holdMessage msg tc1)
    hNoT hScT hHead ((SystemState.getReply?_eq_some_iff _ _ _).mpr hTR)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTC)
    (fun b hb => hBelow b (by rw [hHeadC] at hb; exact hb))
  have hPt := returnUnheldSchedContextInPlace_tcbAt T c scId hNoT hTc' hRtT
  have hFr := returnUnheldSchedContextInPlace_popFrame T c scId hNoT
  generalize returnUnheldSchedContextInPlace T c scId = Rr at hPt hPr hFr
  have hAgS := SchedContextOps.settleReturnedContext_agree Rr home scId
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  generalize SchedContextOps.settleReturnedContext Rr home scId = P at hAgS hF
  have hPt' : P.objects[tid.toObjId]? = some (.tcb rtT) :=
    releaseAgreeAt_of_not_sc hAgS hPt (fun _ e => by cases e)
  have hPr' : P.objects[rid.toObjId]? =
      some (.reply { rp.consumed with prev := none, next := none }) :=
    releaseAgreeAt_of_not_sc hAgS hPr (fun _ e => by cases e)
  have hComb : ∀ x, x ≠ c.toObjId → x ≠ rid.toObjId →
      (P.objects[x]?).map popFieldsView = (st.objects[x]?).map popFieldsView :=
    fun x hx hy => (hF.2.2.2 x).trans (popAgreeAt_of_runLinks (hView x hx hy))
  obtain ⟨tcP, hPC, ecP⟩ := popAgreeAt_tcb (hF.2.2.2 c.toObjId) hTC
  refine ⟨popAgreeAt_endpoint (hComb _ hEc hEr) hE, ⟨rtT, hPt', ?_, ?_⟩, ?_⟩
  · have : receiveBlockAdmits rtT = receiveBlockAdmits rtT.withoutRunLinks := rfl
    rw [this, eT]; exact hA
  · show rtT.withoutRunLinks.boundNotificationCode = rt.withoutRunLinks.boundNotificationCode
    rw [eT]
  · unfold receiveBlocksInPlace
    have hKP : P.objectsKeepFinds st := hF.2.2.1.trans hKT
    have hV : ∀ x, P.getObjectType? x = st.getObjectType? x := by
      intro x
      by_cases hxc : x = c.toObjId
      · subst hxc; unfold SystemState.getObjectType?; rw [hPC, hT]; rfl
      · by_cases hxr : x = rid.toObjId
        · subst hxr; unfold SystemState.getObjectType?; rw [hPr', hRp]; rfl
        · exact getObjectType?_of_popAgree (hComb x hxc hxr)
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ hKP hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      by_cases hpc : p.toObjId = c.toObjId
      · exact Option.isSome_iff_exists.mpr
          ⟨tcP, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hpc ▸ hPC)⟩
      · by_cases hpr : p.toObjId = rid.toObjId
        · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
          have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
          rw [hpr, hRp] at this; cases this
        · exact getTcb?_isSome_of_popAgree (hComb _ hpc hpr) hp
    · have hFree : ({ rp.consumed with prev := none, next := none } : Reply).isFree = true := by
        have h := Reply.consumed_caller rp
        simp only [Reply.caller] at h
        simp only [Reply.isFree, Reply.caller, h, Option.isNone_none, Bool.and_self]
      have hSt : P.replyStashedAt rid { rp.consumed with prev := none, next := none } = false := by
        rw [replyStashedAt_eq_stasherTestAt]
        rw [replyStashedAt_eq_stasherTestAt] at hStash
        show (match rp.consumed.stasherCode with
          | 0 => false
          | k + 1 => stasherTestAt P (⟨k⟩ : SeLe4n.ThreadId) (rid.val + 1)) = false
        rw [Reply.consumed_stasherCode]
        revert hStash
        cases rp.stasherCode with
        | zero => intro _; rfl
        | succ k =>
          intro hStash
          dsimp only at hStash ⊢
          by_cases hkc : (⟨k⟩ : SeLe4n.ThreadId).toObjId = c.toObjId
          · unfold stasherTestAt SystemState.getTcb?
            rw [hkc, hPC]
            have e := congrArg TCB.ipcStateCode ecP
            simp only [TCB.withoutRunLinks] at e
            simp only [e]
            show ((holdMessage msg tc1).ipcStateCode == 1 && _) = false
            have e2 : (holdMessage msg tc1).ipcStateCode = tc1.ipcStateCode := rfl
            simp only [e2, hc1, receiverReady, TCB.setIpcState_ipcStateCode]
            rfl
          · by_cases hkr : (⟨k⟩ : SeLe4n.ThreadId).toObjId = rid.toObjId
            · unfold stasherTestAt SystemState.getTcb?; rw [hkr, hPr']
            · rw [stasherTestAt_of_popAgree (hComb _ hkc hkr)]; exact hStash
      simp only [SystemState.replyStashValid]
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hPr']
      simp only [hSt, hFree]
      rfl
    · show replyRecordsInPlace _ (rid.val + 1) = true
      simp only [replyRecordsInPlace, Bool.and_eq_true] at hRec ⊢
      exact ⟨(hKP _).trans hRec.1, storeLeavesIndexAndTypes_of_frame hV hRec.2⟩

/-- **The reply-receive answering a caller recording no server, in place**:
under `replyUnheldPopsInPlace`, with no sender waiting and the replier's block
admissible (read on the pre-state and carried across the reply leg and the
pop, `popUnheldSettled_receiveGuard`), the specification's reply-receive is
the reply leg's writes, the unheld pop and its settle on the caller's home
core, the replier's block, its priority walk and the caller's staged message.
No holder loses a context, so none is taken off its core. -/
theorem replyRecvAnsweringOnCore_unheld_inPlace
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : answer = none →
      replyTransferInert st tid ct grant = true) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvStageLast answer
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true (replyRecvFaultFirst answer
              (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
                (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
                (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) c) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true (replyRecvFaultFirst answer
              (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
                (storeReplyLeg st c rid msg) c ⟨replyHeadContextCode st rid - 1⟩)
                (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) c) tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId := by
  obtain ⟨rp', scId, hRp', hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, hPopR, hAppl⟩ :=
    replyUnheldPopsInPlace_pop st c rid msg ct hT hG
  rw [hRp] at hRp'
  cases hRp'
  obtain ⟨rp2, scId2, sc, hRp2, hN2, hScO, hHead, hBelow⟩ := replyUnheldPopsInPlace_stack st c rid hG
  rw [hRp] at hRp2
  cases hRp2
  rw [hN] at hN2
  injection hN2 with hN2
  injection hN2 with hN2
  subst hN2
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st tid c none ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  obtain ⟨hE1, ⟨rt1, hR1, hA1, hB1⟩, hG1⟩ := popUnheldSettled_receiveGuard st c tid rid msg ct rp
    epId ep rt scId sc (determineTargetCore st c) hNo hT hFC hRp hN hScO hHead hBelow hNe hE hR
    hA hEnq hStash hRec
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hXf := replyRecvReplyTransfer_of_inert answer st tid c grant ct hTc hInert
  have hRecS : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hNoP := settleReturnedContext_noResizeDue _ (determineTargetCore st c) scId
    (returnUnheldSchedContextInPlace_noResizeDue _ c scId (storeReplyLeg_noResizeDue st c rid msg hNo))
  rw [← storeReplyLeg_eq_hold _ _ _ _ hNo] at hPopR
  simp only [SystemState.unlinkReplyWaiterOpt] at hEq
  generalize hS1 : storeReplyLeg st c rid msg = S1 at hEq hPopR hE1 hR1 hG1 hNoP
  generalize hP : SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace S1 c scId)
    (determineTargetCore st c) scId = P at hPopR hE1 hR1 hG1 hNoP
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1, hNoY⟩ : (replyRecvFaultFirst answer P c).objects[epId]? =
        some (.endpoint ep) ∧
      (∃ rt', (replyRecvFaultFirst answer P c).objects[tid.toObjId]? = some (.tcb rt') ∧
        receiveBlockAdmits rt' = true) ∧
      receiveBlocksInPlace (replyRecvFaultFirst answer P c) epId tid ep.receiveQ.tail (some rid) =
        true ∧ (replyRecvFaultFirst answer P c).objects.noResizeDue := by
    cases answer with
    | none => exact ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1, hNoP⟩
    | some f =>
      obtain ⟨hF, hNoA⟩ := faultReplyApplyOnCore_answerGuardFrame P c f hNoP
      obtain ⟨a, ⟨r, b, d, -⟩, e⟩ := receiveGuard_of_answerGuardFrame hF (hNe)
        hE1 hR1 hA1 hG1
      exact ⟨a, ⟨r, b, d⟩, e, hNoA⟩
  generalize hY : replyRecvFaultFirst answer P c = Y at hE1 hR1 hG1 hNoY
  obtain ⟨hE2, ⟨rt2, hR2, hA2⟩, hG2⟩ := receiveReturnSchedContext_receiveGuard true Y tid hNoY
    hE1 hR1 hA1 hG1
  generalize hQ : receiveReturnSchedContext true Y tid = Q at hE2 hR2 hG2
  have hEp1 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt2 (some rid) core hE2 hS hR2 hA2 hG2]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked Q epId ep tid rt2 (some rid) core hE2 hR2
    hA2 hG2
  refine ⟨?_, tb, hTb, hBk⟩
  have hRes : tid.isReserved = false := by
    have h := hG2
    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1
  cases answer with
  | none =>
    have hNoQ : Q.objects.noResizeDue := hQ ▸ receiveReturnSchedContext_noResizeDue true Y tid hNoY
    have hSnd0 : receiveRendezvousSender? Q epId = none := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [replyRecvFaultFirst] at hY
    subst hY
    rw [endpointReplyRecvAnsweringOnCore_answerFirst_at none epId tid rid c msg grant core st
      (by simp) (Ne.symm hNe) hEq hPopR (hXf P) hNoP (by rw [hQ, hSnd0]; simp)
      (fun _ => .inr ⟨by rw [hQ]; unfold receiveCapRequest; rw [hSnd0], fun s0 E hE => ?_⟩)]
    · simp only [hRecS, Option.getD_none, hQ, hRecv]
      simp [replyRecvPostReceiveDonation_none_self _ _ _ _ hRes, applyReceiveLegPipHandoff,
        replyRecvAnswerCaller, replyRecvStageLast]
    · simp only [hRecS, Option.getD_none, hQ, hRecv] at hE
      simp [replyRecvPostReceiveDonation_none_self _ _ _ _ hRes, applyReceiveLegPipHandoff] at hE
      obtain ⟨-, rfl⟩ := hE
      exact ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core
        (removeRunnableOnCore_noResizeDue _ _ _ (storeReceiveBlock_noResizeDue _ _ _ _ _ hNoQ))).trans
        ((ipcBufferReadsAgree_removeRunnableOnCore _ tid core).trans
          ((ipcBufferReadsAgree_storeReceiveBlock Q epId tid _ _ hNoQ).trans
            (hQ ▸ ipcBufferReadsAgree_receiveReturnSchedContext true _ tid hNoP)))).words
  | some f =>
    simp only [replyRecvFaultFirst] at hY
    unfold endpointReplyRecvAnsweringOnCore
    simp only [hRecS, Option.getD_none, hEq, hPopR, hXf, replyRecvAnswerCaller, hY, hQ, hRecv,
      Option.bind_some, hS, replyRecvPostReceiveDonation_none_self _ _ _ _ hRes]
    simp [applyReceiveLegPipHandoff, replyRecvStageLast]

/-- **The reply leg to a caller recording no server carries the receive's
guard** (WS-SX SX8.3): on the state the reply leg alone leaves (`storeReplyLeg`,
no server's reply waiters to leave and no pop), the endpoint is as it was, the
replier may block on it and its block writes in place, each read on the
pre-state.  `storeReplyRendezvous_receiveGuard` without the unlink. -/
theorem storeReplyLeg_receiveGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (rt : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hFree : rp.consumed.isFree = true) (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (storeReplyLeg st c rid msg).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt1, (storeReplyLeg st c rid msg).objects[tid.toObjId]? = some (.tcb rt1) ∧
        receiveBlockAdmits rt1 = true ∧ rt1.boundNotificationCode = rt.boundNotificationCode) ∧
      receiveBlocksInPlace (storeReplyLeg st c rid msg) epId tid ep.receiveQ.tail
        (some rid) = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hTc' : tid.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hTr : tid.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hR; cases hR
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo]
  generalize hS1 : storeReplyLegReady st c rid = S1
  have hAg := fun x hx hy => hS1 ▸ storeReplyLegReady_agree st c rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hHold _ hEc]; exact agreeAt_of_not_tcb (hAg _ hEc hEr) (fun _ e => by cases e) hE
  · obtain ⟨rt1, h1, e1⟩ := agreeAt_tcb (hAg _ hTc' hTr) hR
    refine ⟨rt1, by rw [hHold _ hTc']; exact h1, ?_, ?_⟩
    · have : receiveBlockAdmits rt1 = receiveBlockAdmits rt1.withoutRunLinks := rfl
      rw [this, e1]; exact hA
    · show rt1.withoutRunLinks.boundNotificationCode = rt.withoutRunLinks.boundNotificationCode
      rw [e1]
  · unfold receiveBlocksInPlace
    rw [Bool.and_eq_true, Bool.and_eq_true]
    have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyLegReady_keepsFinds st c rid hNo hFC
    obtain ⟨tc1, htc1, hcv⟩ := hS1 ▸ storeReplyLegReady_callerView st c rid ct hNo hTc hFC hRc
    have hc1 : tc1.ipcStateCode = (receiverReady ct).ipcStateCode := by
      have h := congrArg TCB.ipcStateCode hcv; exact h
    have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
      hS1 ▸ storeReplyLegReady_reply st c rid ct rp hNo hTc hFC hRp hRc
    have hAt : ∀ x, (x = c.toObjId ∧
          ∃ t, (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.tcb t) ∧
            t.ipcStateCode = (receiverReady ct).ipcStateCode) ∨
        (x = rid.toObjId ∧
          (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.reply rp.consumed)) ∨
        ((S1.mapTcbInPlace c (holdMessage msg)).objects[x]?).map KernelObject.withoutRunLinks =
          (st.objects[x]?).map KernelObject.withoutRunLinks := by
      intro x
      by_cases hxc : x = c.toObjId
      · subst hxc
        left
        refine ⟨rfl, holdMessage msg tc1, ?_, hc1⟩
        rw [SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
      · by_cases hxr : x = rid.toObjId
        · subst hxr; right; left; rw [hHold _ hxc]; exact ⟨rfl, hR1⟩
        · right; right; rw [hHold _ hxc]; exact hAg x hxc hxr
    have hV : ∀ x, (S1.mapTcbInPlace c (holdMessage msg)).getObjectType? x =
        st.getObjectType? x := by
      intro x
      rcases hAt x with ⟨e, t, h, _⟩ | ⟨e, h⟩ | h
      · subst e; unfold SystemState.getObjectType?; rw [h, hT]; rfl
      · subst e; unfold SystemState.getObjectType?; rw [h, hRp]; rfl
      · exact getObjectType?_of_view h
    have hKF : (S1.mapTcbInPlace c (holdMessage msg)).objectsKeepFinds st :=
      (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
    refine ⟨⟨enqueuesInPlace_of_frame _ _ _ hKF hV ?_ hEnq, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
      have h1 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
      rcases hAt p.toObjId with ⟨_, t', h, _⟩ | ⟨e, _⟩ | h
      · exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h⟩
      · rw [e, hRp] at h1; cases h1
      · obtain ⟨t', h', _⟩ := agreeAt_tcb h h1
        exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
    · have hSt : (S1.mapTcbInPlace c (holdMessage msg)).replyStashedAt rid rp.consumed = false := by
        rw [replyStashedAt_eq_stasherTestAt, Reply.consumed_stasherCode]
        rw [replyStashedAt_eq_stasherTestAt] at hStash
        revert hStash
        cases rp.stasherCode with
        | zero => intro _; rfl
        | succ k =>
          intro hStash
          dsimp only at hStash ⊢
          rcases hAt (⟨k⟩ : SeLe4n.ThreadId).toObjId with ⟨_, t, h, hc⟩ | ⟨_, h⟩ | h
          · unfold stasherTestAt SystemState.getTcb?; rw [h]
            simp only [hc, receiverReady, TCB.setIpcState_ipcStateCode]
            rfl
          · unfold stasherTestAt SystemState.getTcb?; rw [h]
          · rw [stasherTestAt_of_view h]; exact hStash
      simp only [SystemState.replyStashValid]
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr (by rw [hHold _ hRc]; exact hR1)]
      simp only [hSt, hFree]
      rfl
    · show replyRecordsInPlace _ (rid.val + 1) = true
      simp only [replyRecordsInPlace, Bool.and_eq_true] at hRec ⊢
      exact ⟨(hKF _).trans hRec.1, storeLeavesIndexAndTypes_of_frame
        (s' := S1.mapTcbInPlace c (holdMessage msg)) hV hRec.2⟩

/-- **The reply-receive answering a caller recording no server whose reply
object is linked to nothing, in place** (WS-SX SX8.3): seL4-MCS's
`doReplyTransfer` with `reply_remove` on a reply object neither heading a stack
nor sitting on one (nothing to pop), then `receiveIPC` blocking the replier.
Under `replyUnlinkedInPlace`, with no sender waiting and the replier's block
admissible (read on the pre-state, carried across the reply leg by
`storeReplyLeg_receiveGuard`), the composite answering the caller with
`answer` is the reply leg's writes, the replier's block, its priority walk and
the caller answered. -/
theorem replyRecvAnsweringOnCore_unlinked_inPlace
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId)
    (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnlinkedInPlace st c rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : answer = none →
      replyTransferInert st tid ct grant = true) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvStageLast answer
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true (replyRecvFaultFirst answer (storeReplyLeg st c rid msg) c)
              tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c 0) ∧
      ∃ x, (removeRunnableOnCore (storeReceiveBlock
            (receiveReturnSchedContext true (replyRecvFaultFirst answer (storeReplyLeg st c rid msg) c)
              tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).getTcb? tid = some x ∧
        x.ipcState = .blockedOnReceive epId := by
  have hW : replyWakesInPlace st c ct rid = true := hG
  have hNo := replyWakesInPlace_noResizeDue hW
  have hG' := hG
  simp only [replyUnlinkedInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
  obtain ⟨⟨⟨⟨⟨hCRes, hLC⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG'
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
  obtain ⟨hNext, hPrev⟩ := hRpG
  have hFree : rp.consumed.isFree = true := by
    rw [← Reply.consumedIsFree_eq]; simp only [Reply.consumedIsFree, hNext]
  obtain ⟨hEq, hR5⟩ := replyOnCore_eq_storeLeg st tid c none ct ep0 rid rp msg core hSz hT hIpc
    hRO hCRes hLC hFC hLR hFR hRp (Or.inl ⟨hNext, hPrev⟩)
  simp only [SystemState.unlinkReplyWaiterOpt] at hEq hR5
  have hHead : replyFrameHeadContext? (storeReplyLeg st c rid msg) rid = none := by
    unfold replyFrameHeadContext?
    rw [hR5]
    simp only [Reply.consumed, hNext]
  obtain ⟨hE0, ⟨rt0, hR0, hA0, -⟩, hG0⟩ := storeReplyLeg_receiveGuard st c tid rid msg ct rp
    epId ep rt hNo hT hFC hRp hNe hE hR hA hEnq hFree hStash hRec
  have hNoP := storeReplyLeg_noResizeDue st c rid msg hNo
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hXf := replyRecvReplyTransfer_of_inert answer st tid c grant ct hTc hInert
  have hRecS : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  generalize hS1 : storeReplyLeg st c rid msg = S1 at hEq hHead hE0 hR0 hG0 hNoP
  have hPop : replyRecvPopDonation rid c S1 = .ok (none, S1) := by
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
  have hE1 := hE0
  have hG1 := hG0
  obtain ⟨rt1, hR1, hA1⟩ : ∃ r, S1.objects[tid.toObjId]? = some (.tcb r) ∧
      receiveBlockAdmits r = true := ⟨rt0, hR0, hA0⟩
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1, hNoY⟩ : (replyRecvFaultFirst answer S1 c).objects[epId]? =
        some (.endpoint ep) ∧
      (∃ rt', (replyRecvFaultFirst answer S1 c).objects[tid.toObjId]? = some (.tcb rt') ∧
        receiveBlockAdmits rt' = true) ∧
      receiveBlocksInPlace (replyRecvFaultFirst answer S1 c) epId tid ep.receiveQ.tail (some rid) =
        true ∧ (replyRecvFaultFirst answer S1 c).objects.noResizeDue := by
    cases answer with
    | none => exact ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1, hNoP⟩
    | some f =>
      obtain ⟨hF, hNoA⟩ := faultReplyApplyOnCore_answerGuardFrame S1 c f hNoP
      obtain ⟨a, ⟨r, b, d, -⟩, e⟩ := receiveGuard_of_answerGuardFrame hF (hNe)
        hE1 hR1 hA1 hG1
      exact ⟨a, ⟨r, b, d⟩, e, hNoA⟩
  generalize hY : replyRecvFaultFirst answer S1 c = Y at hE1 hR1 hG1 hNoY
  obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := receiveReturnSchedContext_receiveGuard true Y tid hNoY
    hE1 hR1 hA1 hG1
  have hEp1 : (receiveReturnSchedContext true Y tid).getEndpoint? epId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE1
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core
      (receiveReturnSchedContext true Y tid) =
      (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true Y tid) epId tid
        ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq _ epId ep tid rt1 (some rid) core hE1 hS hR1 hA1 hG1]
    have hSnd : (receiveRendezvousSender? (receiveReturnSchedContext true Y tid) epId).isNone =
        true := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked _ epId ep tid rt1 (some rid) core hE1 hR1
    hA1 hG1
  refine ⟨?_, tb, hTb, hBk⟩
  have hRes : tid.isReserved = false := by
    have h := hG1
    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1.1.1.1.1.1
  cases answer with
  | none =>
    have hNoQ := receiveReturnSchedContext_noResizeDue true Y tid hNoY
    have hSnd0 : receiveRendezvousSender? (receiveReturnSchedContext true Y tid) epId = none := by
      simp [receiveRendezvousSender?, hEp1, hS]
    simp only [replyRecvFaultFirst] at hY
    subst hY
    rw [endpointReplyRecvAnsweringOnCore_answerFirst_at none epId tid rid c msg grant core st
      (by simp) (Ne.symm hNe) hEq hPop (hXf S1) hNoP (by rw [hSnd0]; simp)
      (fun _ => .inr ⟨by unfold receiveCapRequest; rw [hSnd0], fun s0 E hE => ?_⟩)]
    · simp only [hRecS, Option.getD_none, hRecv]
      simp [replyRecvPostReceiveDonation_none_self _ _ _ _ hRes, applyReceiveLegPipHandoff,
        replyRecvAnswerCaller, replyRecvStageLast]
    · simp only [hRecS, Option.getD_none, hRecv] at hE
      simp [replyRecvPostReceiveDonation_none_self _ _ _ _ hRes, applyReceiveLegPipHandoff] at hE
      obtain ⟨-, rfl⟩ := hE
      exact ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core
        (removeRunnableOnCore_noResizeDue _ _ _ (storeReceiveBlock_noResizeDue _ _ _ _ _ hNoQ))).trans
        ((ipcBufferReadsAgree_removeRunnableOnCore _ tid core).trans
          ((ipcBufferReadsAgree_storeReceiveBlock _ epId tid _ _ hNoQ).trans
            (ipcBufferReadsAgree_receiveReturnSchedContext true _ tid hNoP)))).words
  | some f =>
    simp only [replyRecvFaultFirst] at hY
    unfold endpointReplyRecvAnsweringOnCore
    simp only [hRecS, Option.getD_none, hEq, hPop, hXf, replyRecvAnswerCaller, hY, hRecv,
      Option.bind_some, hS, replyRecvPostReceiveDonation_none_self _ _ _ _ hRes]
    simp [applyReceiveLegPipHandoff, replyRecvStageLast]

/-! ### The pop's admission, from each arm's in-place guard

WS-SX SX33.  The reply-receive reads its pop's admission
(`replyRecvPopAdmits`) on the entry state, before the reply leg writes.  Each
arm's in-place guard already reads the pop it commits, so it implies the
admission, with no invariant: the fast forms keep their unconditional
equalities. -/


/-- The caller's frame test, where its reply link is the frame. -/
theorem replyRecvCallerFrameIs_of_link {st : SystemState} {c : SeLe4n.ThreadId} {ct : TCB}
    {rid : SeLe4n.ReplyId} (hT : st.getTcb? c = some ct) (hRO : ct.replyObject = some rid) :
    replyRecvCallerFrameIs st c rid = true := by
  unfold replyRecvCallerFrameIs lookupTcb
  split
  · next t ht =>
    split at ht
    · cases ht
    · rw [hT] at ht; cases ht; simp [hRO]
  · rfl

/-- **A reply whose frame links to nothing admits its pop**: it pops nothing. -/
theorem replyRecvPopAdmits_of_wakes {st : SystemState} {c : SeLe4n.ThreadId} {ct : TCB}
    {rid : SeLe4n.ReplyId} (hT : st.getTcb? c = some ct) (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true) : replyRecvPopAdmits st rid c = true := by
  have hH : replyFrameHeadContext? st rid = none := by
    unfold replyWakesInPlace at hG
    simp only [Bool.and_eq_true] at hG
    have hM := hG.2
    unfold replyFrameHeadContext?
    cases hR : st.getReply? rid with
    | none => rfl
    | some rp =>
      rw [hR] at hM
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hM
      simp [hM.1]
  unfold replyRecvPopAdmits replyRecvPopAdmitsCore
  rw [replyRecvCallerFrameIs_of_link hT hRO, replyFrameHeadHolder?_of_no_head _ _ hH]
  simp [hH]

theorem threadId_toValid?_isSome {t : SeLe4n.ThreadId} (h : t.isReserved = false) :
    t.toValid?.isSome = true := by
  unfold SeLe4n.ThreadId.toValid?
  split
  · next e => subst e; simp [SeLe4n.ThreadId.isReserved, SeLe4n.ThreadId.sentinel] at h
  · rfl

/-- **A reply returning the caller's lent context admits its pop**
(`replyPopsInPlace`, read on the entry state). -/
theorem replyRecvPopAdmits_of_pops {st : SystemState} {c server : SeLe4n.ThreadId} {ct : TCB}
    {rid : SeLe4n.ReplyId} (hT : st.getTcb? c = some ct) (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true) :
    replyRecvPopAdmits st rid c = true := by
  have hCRes : c.isReserved = false := by
    unfold replyPopsInPlace at hG; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
    exact hG.1.1.1.1.1.1.1.1.1
  obtain ⟨scId, _, hHH, hDC, _⟩ := replyPopsInPlace_pop st c server rid ct hT hSRes hG
  unfold replyRecvPopAdmits replyRecvPopAdmitsCore
  rw [replyRecvCallerFrameIs_of_link hT hRO, hHH]
  simp only [threadId_toValid?_isSome hSRes, threadId_toValid?_isSome hCRes,
    donatedReturnCommits_recipientAcceptable hDC, ↓reduceIte, hDC, Bool.and_self]

/-- **A reply whose server keeps the context admits its pop**
(`replyHeldPopsInPlace`, read on the entry state). -/
theorem replyRecvPopAdmits_of_heldPops {st : SystemState} {c server : SeLe4n.ThreadId}
    {ct : TCB} {rid : SeLe4n.ReplyId} (hT : st.getTcb? c = some ct)
    (hRO : ct.replyObject = some rid)
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode server rid = true) :
    replyRecvPopAdmits st rid c = true := by
  unfold replyHeldPopsInPlace at hG
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨hCRes, _⟩, hCB⟩, _⟩, _⟩, _⟩, _⟩, hM⟩ := hG
  cases hR : st.getReply? rid with
  | none => rw [hR] at hM; cases hM
  | some rp =>
  rw [hR] at hM
  simp only [] at hM
  cases hN : rp.next with
  | none => rw [hN] at hM; cases hM
  | some l =>
  cases l with
  | frame _ => rw [hN] at hM; cases hM
  | head scId =>
  rw [hN] at hM
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hM
  obtain ⟨⟨hScM, hOutC⟩, hKept⟩ := hM
  obtain ⟨hKC, _⟩ := keptPopsInPlace_pop st server scId hKept
  obtain ⟨sc, rid0, rp0, ht, hSc, hB, hSR, hR0, hN0, hBelow, _, hSRes, hHt, _⟩ :=
    keptPopsInPlace_spec st server scId hKept
  rw [hSc] at hScM
  simp only [hSR, beq_iff_eq] at hScM
  have hRid : rid0 = rid := by cases rid0; cases rid; simp_all
  subst hRid
  rw [hR] at hR0; cases hR0
  have hHC : replyFrameHeadContext? st rid0 = some scId := by
    unfold replyFrameHeadContext?; rw [hR]; simp [hN, hSc, hSR]
  have hHH := replyFrameHeadHolder?_of_head st rid0 scId server hHC (by rw [hSc]; exact hB)
  have hRes := (replyStackOuterCaller?_of_head st scId sc rid0 rp hSc hSR hR hN
    (fun b hb => (hBelow b hb).2.1)).2
  have hAcc : donationRecipientAcceptable st c = false := by
    rw [donationRecipientAcceptable_eq_of_some st c ct
      (by unfold lookupTcb; rw [if_neg (by simp [hCRes]), hT])]
    unfold TCB.schedContextBinding SchedContextBinding.ofCodes
    cases h0 : ct.scBindingScCode with
    | zero => exact absurd h0 hCB
    | succ k => cases ct.scBindingOwnerCode <;> rfl
  have hNot : keptPopOuterIsNot st server scId c = true := by
    unfold keptPopOuterIsNot
    rw [hRes]
    simp only [bne_iff_ne, ne_eq]
    rw [heldPopOuter?_of_getTcb hHt]
    unfold heldPopOwner?
    split
    · intro e
      apply hOutC
      unfold SeLe4n.ThreadId.ofOptCode at e
      split at e
      · cases e
      · next k hk => cases e; exact hk
    · simp
  unfold replyRecvPopAdmits replyRecvPopAdmitsCore
  rw [replyRecvCallerFrameIs_of_link hT hRO, hHH]
  simp only [threadId_toValid?_isSome hSRes, threadId_toValid?_isSome hCRes, hAcc, hKC, hNot,
    Bool.false_eq_true, ↓reduceIte, Bool.and_self]

/-- **A reply whose frame heads an unheld context admits its pop**
(`replyUnheldPopsInPlace`, read on the entry state). -/
theorem replyRecvPopAdmits_of_unheldPops {st : SystemState} {c : SeLe4n.ThreadId}
    {ct : TCB} {rid : SeLe4n.ReplyId} (hT : st.getTcb? c = some ct)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true) :
    replyRecvPopAdmits st rid c = true := by
  unfold replyUnheldPopsInPlace at hG
  simp only [Bool.and_eq_true] at hG
  obtain ⟨_, hM⟩ := hG
  cases hR : st.getReply? rid with
  | none => rw [hR] at hM; cases hM
  | some rp =>
  rw [hR] at hM
  simp only [] at hM
  cases hN : rp.next with
  | none => rw [hN] at hM; cases hM
  | some l =>
  cases l with
  | frame _ => rw [hN] at hM; cases hM
  | head s =>
  rw [hN] at hM
  simp only [Bool.and_eq_true] at hM
  obtain ⟨hScM, hU⟩ := hM
  cases hSc : st.getSchedContext? s with
  | none => rw [hSc] at hScM; cases hScM
  | some sc =>
  rw [hSc] at hScM
  simp only [] at hScM
  have hSR : sc.scReply = some rid := by
    cases h0 : sc.scReply with
    | none => rw [h0] at hScM; cases hScM
    | some h =>
      rw [h0] at hScM
      have : h.val = rid.val := by simpa using hScM
      cases h; cases rid; simp_all
  have hHC : replyFrameHeadContext? st rid = some s := by
    unfold replyFrameHeadContext?; rw [hR]; simp [hN, hSc, hSR]
  have hBT : sc.boundThreadCode = 0 := by
    have h := hU
    unfold unheldPopsInPlace at h
    simp only [Bool.and_eq_true, hSc, beq_iff_eq] at h
    exact h.2.1
  have hHH : replyFrameHeadHolder? st rid = none := by
    unfold replyFrameHeadHolder?; rw [hHC]
    simp [hSc, SchedContext.boundThread, hBT, SeLe4n.ThreadId.ofOptCode]
  have hRC := (unheldPopsInPlace_pop st s c hU).1
  unfold replyRecvPopAdmits replyRecvPopAdmitsCore
  rw [replyRecvCallerFrameIs_of_link hT hRO, hHH, hHC]
  unfold unheldPopCommits
  simp only [donationRecipientAcceptable_of_unheldReturnCommits hRC, hRC, ↓reduceIte,
    Bool.and_self]

/-- **The reply arm of a reply-receive**: what the reply leg pops, read on the
pre-state.  An enumeration, so choosing an arm allocates nothing: the context
the donated and unheld arms return and the held arm keeps, and the caller's
home core, enter the pop as arguments (`ReplyRecvArm.pop`). -/
inductive ReplyRecvArm where
  /-- The caller recorded the server and lent it nothing. -/
  | rendezvous
  /-- The caller lent the server its context; the pop returns it. -/
  | donated
  /-- The server keeps the context the reply object heads. -/
  | held
  /-- The caller recorded no server; the context no thread holds returns to it. -/
  | unheld
  /-- The caller recorded no server; its reply object links to nothing. -/
  | unlinked

namespace ReplyRecvArm

/-- Whether the arm's caller recorded the server (the reply leg's rendezvous). -/
@[inline] def recordsServer : ReplyRecvArm → Bool
  | .rendezvous => true
  | .donated => true
  | .held => true
  | .unheld => false
  | .unlinked => false

/-- The reply leg's writes, the caller woken holding no message yet. -/
@[inline] def legReady (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  if arm.recordsServer then storeReplyRendezvousReady st c tid rid else storeReplyLegReady st c rid

/-- The reply leg as the specification runs it, the caller holding `msg`. -/
@[inline] def leg (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) : SystemState :=
  if arm.recordsServer then storeReplyRendezvous st c tid rid msg else storeReplyLeg st c rid msg

/-- The arm's pop, after the reply leg. -/
@[inline] def pop : ReplyRecvArm → SystemState → SeLe4n.ThreadId → SeLe4n.ThreadId →
    SeLe4n.SchedContextId → CoreId → SystemState
  | .rendezvous, X, _, _, _, _ => X
  | .donated, X, c, tid, scId, home => popDonationSettledInPlace X c tid scId home
  | .held, X, _, tid, scId, _ => keepDonatedSchedContextInPlace X tid scId
  | .unheld, X, c, _, scId, home =>
      SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace X c scId) home scId
  | .unlinked, X, _, _, _, _ => X

/-- The server's deschedule after its block: only the donated arm's server gave
back the context it ran on. -/
@[inline] def desched : ReplyRecvArm → SystemState → SeLe4n.ThreadId → SystemState
  | .donated, X, tid => descheduleAtPlacement X tid
  | _, X, _ => X

/-- The server's receive block on the state the pop leaves: its context return
on its bound notification, its block on the endpoint, its removal from its
core. -/
@[inline] def blocked (Y : SystemState) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) : SystemState :=
  removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true Y tid) epId tid tailCode
    (SeLe4n.ReplyId.optCode (some rid))) tid core

/-- The receive leg's tail: the block, the arm's deschedule, the priority walk. -/
@[inline] def tail (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore (arm.desched (blocked Y tid rid epId tailCode core)
    tid) tid core).1

/-- The tail as it is compiled: the context return read off the server's code. -/
@[inline] def tailFast (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore (arm.desched (removeRunnableOnCore
    (storeReceiveBlock (receiveReturnSchedContextFast true Y tid.val) epId tid tailCode
      (rid.val + 1)) tid core) tid) tid core).1

theorem tailFast_eq (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) :
    arm.tailFast Y tid rid epId tailCode core = arm.tail Y tid rid epId tailCode core := by
  unfold tailFast tail blocked
  rw [receiveReturnSchedContextFast_eq]
  rfl

/-- **The blocking reply-receive's writes, the caller holding no message**: the
reply leg, the pop and the tail, in place. -/
@[inline] def ready (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) : SystemState :=
  arm.tailFast (arm.pop (arm.legReady st c tid rid) c tid scId home) tid rid epId tailCode core

/-! ### What the arm's writes keep -/

theorem leg_eq_hold (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (hNo : st.objects.noResizeDue) :
    arm.leg st c tid rid msg = (arm.legReady st c tid rid).mapTcbInPlace c (holdMessage msg) := by
  unfold leg legReady
  split
  · exact storeReplyRendezvous_eq_hold _ _ _ _ _ hNo
  · exact storeReplyLeg_eq_hold _ _ _ _ hNo

theorem legReady_noResizeDue (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    (arm.legReady st c tid rid).objects.noResizeDue := by
  unfold legReady
  split
  · exact storeReplyRendezvousReady_noResizeDue _ _ _ _ hNo
  · exact storeReplyLegReady_noResizeDue _ _ _ hNo

theorem leg_noResizeDue (arm : ReplyRecvArm) (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (hNo : st.objects.noResizeDue) :
    (arm.leg st c tid rid msg).objects.noResizeDue := by
  rw [leg_eq_hold _ _ _ _ _ _ hNo, SystemState.mapTcbInPlace_noResizeDue]
  exact legReady_noResizeDue _ _ _ _ _ hNo

theorem ipcBufferReadsAgree_legReady (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (arm.legReady st c tid rid) st := by
  unfold legReady
  split
  · exact ipcBufferReadsAgree_storeReplyRendezvousReady _ _ _ _ hNo
  · exact ipcBufferReadsAgree_storeReplyLegReady _ _ _ hNo

theorem pop_noResizeDue (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (X : SystemState) (c tid : SeLe4n.ThreadId)
    (hNo : X.objects.noResizeDue) : (arm.pop X c tid scId home).objects.noResizeDue := by
  cases arm with
  | rendezvous => exact hNo
  | donated => exact popDonationSettledInPlace_noResizeDue _ _ _ _ _ hNo
  | held => exact keepDonatedSchedContextInPlace_noResizeDue _ _ _ hNo
  | unheld =>
    exact settleReturnedContext_noResizeDue _ _ _
      (returnUnheldSchedContextInPlace_noResizeDue _ _ _ hNo)
  | unlinked => exact hNo

/-- **The pop commutes with a message write to any thread but the server**. -/
theorem pop_msg (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (X : SystemState) (c tid : SeLe4n.ThreadId) (hNo : X.objects.noResizeDue)
    (hR : r ≠ tid) :
    arm.pop (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c tid scId home =
      (arm.pop X c tid scId home).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  cases arm with
  | rendezvous => rfl
  | donated => exact popDonationSettledInPlace_msg r ρ μ π X c tid scId home hNo hR
  | held => exact keepDonatedSchedContextInPlace_msg r ρ μ π X tid scId hNo hR
  | unheld =>
    show SchedContextOps.settleReturnedContext _ home scId = _
    rw [returnUnheldSchedContextInPlace_msg r ρ μ π X c scId hNo, settleReturnedContext_msg]
    rfl
  | unlinked => rfl

/-- **The held pop keeps every read**, as the donation pop does: it writes the
context, the reply links and the holder's binding. -/
theorem ipcBufferReadsAgree_keepDonatedSchedContextInPlace (st : SystemState)
    (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (keepDonatedSchedContextInPlace st holder scId) st := by
  unfold keepDonatedSchedContextInPlace
  split
  · exact .refl st
  split
  · exact .refl st
  rename_i hr _
  split
  · exact .refl st
  rename_i r _
  split
  · exact .refl st
  dsimp only
  refine (ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans ?_
  · exact fun _ => ⟨rfl, rfl⟩
  · exact (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).2
  · exact (ipcBufferReadsAgree_popLinks st scId _ hr r.prev _ _ hNo).1

theorem ipcBufferReadsAgree_pop (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (X : SystemState) (c tid : SeLe4n.ThreadId)
    (hNo : X.objects.noResizeDue) : ipcBufferReadsAgree (arm.pop X c tid scId home) X := by
  cases arm with
  | rendezvous => exact .refl X
  | donated =>
    exact (ipcBufferReadsAgree_settleReturnedContext _ home scId).trans
      (ipcBufferReadsAgree_returnDonatedSchedContextInPlace X tid c scId hNo)
  | held => exact ipcBufferReadsAgree_keepDonatedSchedContextInPlace X tid scId hNo
  | unheld =>
    exact (ipcBufferReadsAgree_settleReturnedContext _ home scId).trans
      (ipcBufferReadsAgree_returnUnheldSchedContextInPlace X c scId hNo)
  | unlinked => exact .refl X

theorem desched_noResizeDue (arm : ReplyRecvArm) (X : SystemState) (tid : SeLe4n.ThreadId)
    (hNo : X.objects.noResizeDue) : (arm.desched X tid).objects.noResizeDue := by
  cases arm <;> first | exact hNo | exact descheduleAtPlacement_noResizeDue _ _ hNo

theorem desched_msg (arm : ReplyRecvArm) (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (X : SystemState) (tid : SeLe4n.ThreadId) :
    arm.desched (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid =
      (arm.desched X tid).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  cases arm <;> first | rfl | exact descheduleAtPlacement_msg _ _ _ _ _ _

theorem desched_ipcStateCarried (arm : ReplyRecvArm) (X : SystemState) (tid : SeLe4n.ThreadId) :
    ipcStateCarried X (arm.desched X tid) := by
  cases arm <;> first | exact descheduleAtPlacement_ipcStateCarried _ _ |
    exact ipcStateCarried_of_objects_eq rfl

theorem ipcBufferReadsAgree_desched (arm : ReplyRecvArm) (X : SystemState)
    (tid : SeLe4n.ThreadId) : ipcBufferReadsAgree (arm.desched X tid) X := by
  cases arm <;> first | exact .refl X | exact ipcBufferReadsAgree_descheduleAtPlacement _ _

theorem blocked_noResizeDue (Y : SystemState) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) (hNo : Y.objects.noResizeDue) :
    (blocked Y tid rid epId tailCode core).objects.noResizeDue :=
  removeRunnableOnCore_noResizeDue _ _ _ (storeReceiveBlock_noResizeDue _ _ _ _ _
    (receiveReturnSchedContext_noResizeDue _ _ _ hNo))

theorem tail_noResizeDue (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : Y.objects.noResizeDue) : (arm.tail Y tid rid epId tailCode core).objects.noResizeDue :=
  propagatePipChainCrossCore_noResizeDue _ _ _ (desched_noResizeDue _ _ _
    (blocked_noResizeDue _ _ _ _ _ _ hNo))

/-- **The block commutes with the caller's held message.** -/
theorem blocked_msg (r : SeLe4n.ThreadId) (msg : IpcMessage) (Y : SystemState)
    (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (hNo : Y.objects.noResizeDue) (hR : r ≠ tid) :
    blocked (Y.mapTcbInPlace r (holdMessage msg)) tid rid epId tailCode core =
      (blocked Y tid rid epId tailCode core).mapTcbInPlace r (holdMessage msg) := by
  have hNoR := receiveReturnSchedContext_noResizeDue true Y tid hNo
  unfold blocked
  rw [receiveReturnSchedContext_msg r id (fun _ => some msg) id true _ tid hNo hR,
    storeReceiveBlock_msg _ _ _ _ _ _ _ hNoR (fun e => hR e.symm), removeRunnableOnCore_msg]

/-- **The tail commutes with the caller's held message.** -/
theorem tail_msg (arm : ReplyRecvArm) (r : SeLe4n.ThreadId) (msg : IpcMessage)
    (Y : SystemState) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) (hNo : Y.objects.noResizeDue)
    (hR : r ≠ tid) :
    arm.tail (Y.mapTcbInPlace r (holdMessage msg)) tid rid epId tailCode core =
      (arm.tail Y tid rid epId tailCode core).mapTcbInPlace r (holdMessage msg) := by
  have hNoR := receiveReturnSchedContext_noResizeDue true Y tid hNo
  have h3 : (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true Y tid) epId tid
      tailCode (SeLe4n.ReplyId.optCode (some rid))) tid core).objects.noResizeDue :=
    blocked_noResizeDue Y tid rid epId tailCode core hNo
  unfold tail blocked
  rw [receiveReturnSchedContext_msg r id (fun _ => some msg) id true _ tid hNo hR,
    storeReceiveBlock_msg _ _ _ _ _ _ _ hNoR (fun e => hR e.symm), removeRunnableOnCore_msg,
    desched_msg, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ (desched_noResizeDue _ _ _ h3)]

theorem ipcBufferReadsAgree_tail (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : Y.objects.noResizeDue) :
    ipcBufferReadsAgree (arm.tail Y tid rid epId tailCode core) Y := by
  have hNoR := receiveReturnSchedContext_noResizeDue true Y tid hNo
  have h3 := blocked_noResizeDue Y tid rid epId tailCode core hNo
  exact (ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core
      (desched_noResizeDue _ _ _ h3)).trans
    ((ipcBufferReadsAgree_desched _ _ tid).trans
      ((ipcBufferReadsAgree_removeRunnableOnCore _ tid core).trans
        ((ipcBufferReadsAgree_storeReceiveBlock _ epId tid tailCode _ hNoR).trans
          (ipcBufferReadsAgree_receiveReturnSchedContext true Y tid hNo))))

/-! ### The arm's guard and its one equality to the specification -/

/-- **What the arm's in-place path asks of the pre-state**, beside the checks
every arm shares: the caller blocked on the reply naming the server or none,
the arm's pop guard, the server's admission to the block, and the popped
context and the caller's home as the specification reads them. -/
def Admits : ReplyRecvArm → SeLe4n.SchedContextId → CoreId → SystemState → SeLe4n.ThreadId →
    SeLe4n.ThreadId → SeLe4n.ReplyId → TCB → TCB → Reply → Prop
  | .rendezvous, _, _, st, tid, c, rid, ct, rt, rp =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧
      replyWakesInPlace st c ct rid = true ∧ tid ≠ c ∧ receiveBlockAdmits rt = true ∧
      rp.consumedIsFree = true
  | .donated, scId, home, st, tid, c, rid, ct, rt, _ =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧ tid.isReserved = false ∧
      replyPopsInPlace st c ct.scBindingScCode tid rid = true ∧ enqueueAdmits rt = true ∧
      scId = ⟨replyHeadContextCode st rid - 1⟩ ∧ home = determineTargetCore st c
  | .held, scId, _, st, tid, c, rid, ct, rt, rp =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid)) ∧ tid.isReserved = false ∧
      replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true ∧
      (rt.scBindingOwnerCode = 0 ∨ rp.prev = none) ∧
      enqueueAdmits rt = true ∧ scId = ⟨replyHeadContextCode st rid - 1⟩
  | .unheld, scId, home, st, tid, c, rid, ct, rt, _ =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 none) ∧
      replyUnheldPopsInPlace st c rid = true ∧ tid ≠ c ∧ receiveBlockAdmits rt = true ∧
      scId = ⟨replyHeadContextCode st rid - 1⟩ ∧ home = determineTargetCore st c
  | .unlinked, _, _, st, tid, c, rid, ct, rt, _ =>
      (∃ ep0, ct.ipcState = .blockedOnReply ep0 none) ∧
      replyUnlinkedInPlace st c rid = true ∧ tid ≠ c ∧ receiveBlockAdmits rt = true

/-- Every arm's guard names a server other than the caller, on a table that
needs no resize. -/
theorem Admits.facts {arm : ReplyRecvArm}
    {scId : SeLe4n.SchedContextId} {home : CoreId} {st : SystemState} {tid c : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {ct rt : TCB} {rp : Reply} (h : arm.Admits scId home st tid c rid ct rt rp)
    (hT : st.objects[c.toObjId]? = some (.tcb ct)) :
    tid ≠ c ∧ st.objects.noResizeDue := by
  cases arm with
  | rendezvous => exact ⟨h.2.2.1, replyWakesInPlace_noResizeDue h.2.1⟩
  | donated =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hNe, hNo, _⟩ :=
      replyPopsInPlace_donation st c tid rid IpcMessage.empty ct hT h.2.1 h.2.2.1
    exact ⟨fun e => hNe e.symm, hNo⟩
  | held =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hNe, hNo, _⟩ :=
      replyHeldPopsInPlace_pop st c tid rid IpcMessage.empty ct hT h.2.2.1
    exact ⟨fun e => hNe e.symm, hNo⟩
  | unheld =>
    obtain ⟨_, _, _, _, _, _, hNo, _⟩ :=
      replyUnheldPopsInPlace_pop st c rid IpcMessage.empty ct hT h.2.1
    exact ⟨h.2.2.1, hNo⟩
  | unlinked =>
    have hW : replyWakesInPlace st c ct rid = true := h.2.1
    exact ⟨h.2.2.1, replyWakesInPlace_noResizeDue hW⟩

/-- **Every arm's guard admits the pop**: the reply-receive's pop admission,
read before the reply leg, holds wherever the arm's in-place guard does. -/
theorem Admits.popAdmits {arm : ReplyRecvArm}
    {scId : SeLe4n.SchedContextId} {home : CoreId} {st : SystemState} {tid c : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {ct rt : TCB} {rp : Reply} (h : arm.Admits scId home st tid c rid ct rt rp)
    (hT : st.objects[c.toObjId]? = some (.tcb ct)) (hRO : ct.replyObject = some rid) :
    replyRecvPopAdmits st rid c = true := by
  have hG : st.getTcb? c = some ct := by unfold SystemState.getTcb?; rw [hT]
  cases arm with
  | rendezvous => exact replyRecvPopAdmits_of_wakes hG hRO h.2.1
  | donated => exact replyRecvPopAdmits_of_pops hG hRO h.2.1 h.2.2.1
  | held => exact replyRecvPopAdmits_of_heldPops hG hRO h.2.2.1
  | unheld => exact replyRecvPopAdmits_of_unheldPops hG hRO h.2.1
  | unlinked => exact replyRecvPopAdmits_of_wakes (ct := ct) hG hRO h.2.1

end ReplyRecvArm

/-- **The blocking reply-receive in place, over every arm**: under the arm's
guard and the checks every arm shares, the composite answering the caller with
`answer` is the arm's reply leg, its pop and the receive's tail, the caller then
answered, the server left blocked on the endpoint.  One equality per arm, each
the arm's own (`replyRecvAnsweringOnCore_blocks_inPlace`,
`replyRecvAnsweringOnCore_donated_inPlace`, `replyRecvAnsweringOnCore_held_inPlace`,
`replyRecvAnsweringOnCore_unheld_inPlace`, `replyRecvAnsweringOnCore_unlinked_inPlace`). -/
theorem replyRecvAnsweringOnCore_arm_inPlace (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId}
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : answer = none → replyTransferInert st tid ct grant = true) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvStageLast answer
        (arm.tail (replyRecvFaultFirst answer (arm.pop (arm.leg st c tid rid msg) c tid scId home) c)
          tid rid epId ep.recvTailCode core) c 0) ∧
      ∃ x, (ReplyRecvArm.blocked
          (replyRecvFaultFirst answer (arm.pop (arm.leg st c tid rid msg) c tid scId home) c) tid rid
          epId ep.recvTailCode core).getTcb? tid = some x ∧ x.ipcState = .blockedOnReceive epId := by
  cases arm with
  | rendezvous =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe, hA, hFree⟩ := hAd
    rw [Reply.consumedIsFree_eq] at hFree
    refine ⟨replyRecvAnsweringOnCore_blocks_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hFree hStash hRec hInert, ?_⟩
    have hNo := replyWakesInPlace_noResizeDue hG
    have hFC : st.objects.findsInPlace c.toObjId = true := by
      simp only [replyWakesInPlace, Bool.and_eq_true] at hG
      exact hG.1.1.1.2
    obtain ⟨hE0, ⟨rt0, hR0, hA0, -⟩, hG0⟩ := storeReplyRendezvous_receiveGuard st c tid rid msg ct
      rp epId ep rt hNo hT hFC hRp hNe hE hR hA hEnq hFree hStash hRec
    obtain ⟨hEy, ⟨rty, hRy, hAy⟩, hGy, hNoY⟩ := replyRecvFaultFirst_receiveGuard answer hNe
      (storeReplyRendezvous_noResizeDue st c tid rid msg hNo) hE0 hR0 hA0 hG0
    obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := receiveReturnSchedContext_receiveGuard true _ tid
      hNoY hEy hRy hAy hGy
    exact receiveBlock_receiver_blocked _ epId ep tid rt1 (some rid) core hE1 hR1 hA1 hG1
  | donated =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, hA, rfl, rfl⟩ := hAd
    exact replyRecvAnsweringOnCore_donated_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hSRes hG hE hS hR hA hEnq hRp hStash hRec hInert
  | held =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, hOwn, hA, rfl⟩ := hAd
    exact replyRecvAnsweringOnCore_held_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hSRes hG hE hS hR hOwn hA hEnq hRp hStash hRec hInert
  | unheld =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe, hA, rfl, rfl⟩ := hAd
    exact replyRecvAnsweringOnCore_unheld_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hStash hRec hInert
  | unlinked =>
    obtain ⟨⟨ep0, hIpc⟩, hG, hNe, hA⟩ := hAd
    exact replyRecvAnsweringOnCore_unlinked_inPlace answer st epId tid c rid msg grant core ct ep0
      rt ep rp hSz hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hStash hRec hInert

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ### The short message -/

/-- **The blocking reply-receive, delivered in the registers, over every arm**:
the arm's writes in place (`ReplyRecvArm.ready`), then the reply's frame
written into the caller's saved registers.  The message is built only where the
caller is, unexpectedly, not ready. -/
@[noinline] def performReplyRecvArmDelivered (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId) : SystemState :=
  let X := arm.ready st c tid rid scId home epId tailCode core
  writeDeliveredFrameIfReady X c (Architecture.regMessageFrame layout rf len badge)
    (fun _ => holdReplyRecvBody X c layout rf len badge)

/-- The arm's writes, the caller then holding `msg`, are the specification's
reply leg, pop and tail. -/
theorem ReplyRecvArm.tail_pop_leg (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) (hNo : st.objects.noResizeDue) (hNe : tid ≠ c) :
    arm.tail (arm.pop (arm.leg st c tid rid msg) c tid scId home) tid rid epId tailCode core =
      (arm.ready st c tid rid scId home epId tailCode core).mapTcbInPlace c (holdMessage msg) := by
  have h1 := arm.legReady_noResizeDue st c tid rid hNo
  rw [arm.leg_eq_hold st c tid rid msg hNo, arm.pop_msg (scId := scId) (home := home) c id (fun _ => some msg) id _ c tid h1
      (fun e => hNe e.symm),
    arm.tail_msg c msg _ tid rid epId tailCode core (arm.pop_noResizeDue (scId := scId) (home := home) _ c tid h1)
      (fun e => hNe e.symm)]
  unfold ReplyRecvArm.ready
  rw [ReplyRecvArm.tailFast_eq]

/-- The server the arm's writes leave is blocked on the endpoint. -/
theorem ReplyRecvArm.ready_blocked (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (epId : SeLe4n.ObjId)
    (tailCode : Nat) (core : CoreId) (hNo : st.objects.noResizeDue) (hNe : tid ≠ c) {x : TCB}
    (hX : (ReplyRecvArm.blocked (arm.pop (arm.leg st c tid rid msg) c tid scId home) tid rid epId tailCode
      core).getTcb? tid = some x) :
    ∃ x', (arm.ready st c tid rid scId home epId tailCode core).getTcb? tid = some x' ∧
      x'.ipcState = x.ipcState := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have h1 := arm.legReady_noResizeDue st c tid rid hNo
  have h2 := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid h1
  rw [arm.leg_eq_hold st c tid rid msg hNo, arm.pop_msg (scId := scId) (home := home) c id (fun _ => some msg) id _ c tid h1
      (fun e => hNe e.symm), ReplyRecvArm.blocked_msg c msg _ tid rid epId tailCode core h2
      (fun e => hNe e.symm), SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hX
  have h3 := ReplyRecvArm.blocked_noResizeDue _ tid rid epId tailCode core h2
  obtain ⟨x1, hX1, e1⟩ := arm.desched_ipcStateCarried _ tid tid x hX
  obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core
    (arm.desched_noResizeDue _ tid h3) tid x1 hX1
  refine ⟨x2, ?_, e2.trans e1⟩
  unfold ReplyRecvArm.ready
  rw [ReplyRecvArm.tailFast_eq]
  exact hX2

/-- **The blocking reply-receive, delivered, over every arm**: under the arm's
guard and a reply of at most four words, the checked arm's result is the
caller's frame written into its saved registers on top of the arm's writes; the
server, blocked on the endpoint, stages nothing. -/
theorem replyRecvOnCore_arm_delivered (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (grant : Bool) (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hSz : ¬ msg.registers.size > maxMessageRegisters) (hSz4 : msg.registers.size ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    (match endpointReplyRecvOnCore epId tid rid c msg grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), writeDeliveredFrameIfReady (arm.ready st c tid rid scId home epId ep.recvTailCode core) c
        (Architecture.returnFrameOfMessage msg 0 0)
        (fun _ => (arm.ready st c tid rid scId home epId ep.recvTailCode core).mapTcbInPlace c
          (holdMessage msg))) := by
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_arm_inPlace arm none st epId tid c rid msg
    grant core ct rt ep rp hAd hSz hT hRO hE hS hR hEnq hRp hStash hRec (fun _ => hInert)
  obtain ⟨x', hX', hB'⟩ := arm.ready_blocked st c tid rid msg epId ep.recvTailCode core hNo hNe hX
  unfold endpointReplyRecvOnCore
  rw [hEq]
  simp only [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller, replyRecvStageLast,
    replyRecvFaultFirst]
  have h1 := arm.legReady_noResizeDue st c tid rid hNo
  have hNoX : (arm.ready st c tid rid scId home epId ep.recvTailCode core).objects.noResizeDue := by
    unfold ReplyRecvArm.ready
    rw [ReplyRecvArm.tailFast_eq]
    exact arm.tail_noResizeDue _ tid rid epId _ core (arm.pop_noResizeDue (scId := scId) (home := home) _ c tid h1)
  rw [arm.tail_pop_leg st c tid rid msg epId ep.recvTailCode core hNo hNe,
    stageDeliveredMessage_holdMessage _ _ _ hNoX hSz4,
    stageDeliveredMessage_writeDeliveredFrameIfReady_blocked _ c tid _ _ 0 hCT x' hX'
      (by rw [hB', hB]; exact fun h => by cases h)]

/-! ### The long message -/

/-- **The receive tail stages the caller's held long message as the long
frame**, the server it blocks staging nothing: on a state `Y` the arm's pop
leaves, staging the caller holding the long message read in `Z` and then the
server is the long frame on the arm's tail, its overflow words read in that
state, which reads every buffer as `Z` does (`hW`). -/
theorem ReplyRecvArm.tail_stagedLong (arm : ReplyRecvArm) (Y Z : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (capInfo : Nat) (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c) (hLen : 5 ≤ len)
    (hW : ipcWordReadsAgree (arm.tail Y tid rid epId tailCode core) Z)
    (hB : ∃ x, (ReplyRecvArm.blocked (Y.mapTcbInPlace c (holdMessage
        { registers := longReplyRecvRegs rf Z tid len, badge := badge })) tid rid epId tailCode
        core).getTcb? tid = some x ∧ x.ipcState = .blockedOnReceive epId) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (arm.tail (Y.mapTcbInPlace c (holdMessage
          { registers := longReplyRecvRegs rf Z tid len, badge := badge })) tid rid epId tailCode
          core) c capInfo) tid 0 =
      deliverLongReplyRecvCapsFrame capInfo (arm.tail Y tid rid epId tailCode core) c rf len tid
        badge := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨t, hT1, hBk⟩ := hB
  have h3 := ReplyRecvArm.blocked_noResizeDue Y tid rid epId tailCode core hNo
  rw [ReplyRecvArm.blocked_msg c _ Y tid rid epId tailCode core hNo (fun e => hNe e.symm),
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x1, hX1, e1⟩ := arm.desched_ipcStateCarried _ tid tid t hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core
    (arm.desched_noResizeDue _ tid h3) tid x1 hX1
  rw [arm.tail_msg c _ Y tid rid epId tailCode core hNo (fun e => hNe e.symm),
    ← deliverLongReplyRecvFrame_eq _ Z c tid rf len badge capInfo
      (arm.tail_noResizeDue Y tid rid epId tailCode core hNo) hW (by omega)]
  unfold deliverLongReplyRecvCapsFrame
  exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x
    (by rw [deliverLongReplyRecvFrame_getTcb?_ne _ _ _ _ _ _ _ _ hCT]; exact hX)
    (by rw [hEq, e1, hBk]; exact fun h => by cases h)

/-- **The long blocking reply-receive, its reply transferring nothing,
delivered over every arm**: the arm's writes in place, then the long frame. -/
@[noinline] def performReplyRecvArmDeliveredLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (core : CoreId) :
    SystemState :=
  deliverLongReplyRecvCapsFrame 0 (arm.ready st c tid rid scId home epId tailCode core) c rf len tid badge

/-- **The long blocking reply-receive, delivered, over every arm**: under the
arm's guard and a message of `len` words, more than four, the checked arm's
result is `performReplyRecvArmDeliveredLong`.  The held arm's long reply is
answered in place here for the first time. -/
theorem replyRecvOnCore_arm_deliveredLong (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hLen : 5 ≤ len) (hSz : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmDeliveredLong arm scId home st c tid rid epId ep.recvTailCode rf len badge
        core) := by
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_arm_inPlace arm none st epId tid c rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core ct rt ep rp hAd hSz
    hT hRO hE hS hR hEnq hRp hStash hRec (fun _ => hInert)
  unfold endpointReplyRecvOnCore
  rw [hEq]
  simp only [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller, replyRecvStageLast,
    replyRecvFaultFirst]
  have h1 := arm.legReady_noResizeDue st c tid rid hNo
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid h1
  have hAP := (arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid h1).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  rw [arm.leg_eq_hold st c tid rid _ hNo, arm.pop_msg (scId := scId) (home := home) c id _ id _ c tid h1
    (fun e => hNe e.symm)] at hX ⊢
  unfold performReplyRecvArmDeliveredLong ReplyRecvArm.ready
  rw [ReplyRecvArm.tailFast_eq]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState)))
    (arm.tail_stagedLong _ st c tid rid epId ep.recvTailCode core rf len badge 0 hNoP hNe hLen
      ((arm.ipcBufferReadsAgree_tail _ tid rid epId ep.recvTailCode core hNoP).words.trans
        hAP.words) ⟨x, hX, hB⟩)

/-! ### The fault answer -/

/-- The reply leg of a fault answer: the reply's writes with no message. -/
@[inline] def ReplyRecvArm.faultLeg (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : SystemState :=
  if arm.recordsServer then storeFaultReplyRendezvous st c tid rid else storeFaultReplyLeg st c rid

theorem ReplyRecvArm.faultLeg_eq (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    arm.faultLeg st c tid rid = arm.leg st c tid rid IpcMessage.empty := by
  unfold ReplyRecvArm.faultLeg ReplyRecvArm.leg
  split <;> rfl

theorem ReplyRecvArm.ipcBufferReadsAgree_leg (arm : ReplyRecvArm) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (hNo : st.objects.noResizeDue) : ipcBufferReadsAgree (arm.leg st c tid rid msg) st := by
  rw [arm.leg_eq_hold st c tid rid msg hNo]
  exact (ipcBufferReadsAgree_mapTcbInPlace _ c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)

/-- **The blocking reply-receive answering a fault, over every arm**: the
reply's writes with no message, the arm's pop, then the fault answer
(`performFaultAnswer`) in the reply step, then the receive's tail — seL4's
`doReplyTransfer` (`handleFaultReply`) before `handleRecv` (WS-SX SX32). -/
@[noinline] def performReplyRecvArmFaultAnswer (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  arm.tailFast (performFaultAnswer (arm.pop (arm.faultLeg st c tid rid) c tid scId home) c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf (Architecture.regMessageLength layout len) 0)
    tid rid epId tailCode core

/-- The server the receive's tail leaves blocked on the state a fault's answer
leaves, as the arm's guard reads it, stays blocked through the arm's
deschedule and the priority walk. -/
theorem ReplyRecvArm.tail_blocked (arm : ReplyRecvArm) (Y : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (hNo : Y.objects.noResizeDue) {x : TCB}
    (hX : (ReplyRecvArm.blocked Y tid rid epId tailCode core).getTcb? tid = some x) :
    ∃ x', (arm.tail Y tid rid epId tailCode core).getTcb? tid = some x' ∧ x'.ipcState = x.ipcState := by
  have h3 := ReplyRecvArm.blocked_noResizeDue _ tid rid epId tailCode core hNo
  obtain ⟨x1, hX1, e1⟩ := arm.desched_ipcStateCarried _ tid tid x hX
  obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core
    (arm.desched_noResizeDue _ tid h3) tid x1 hX1
  exact ⟨x2, hX2, e2.trans e1⟩

/-- **The blocking reply-receive answering a fault is the specification's, over
every arm**, and it stages nothing for the server, which the receive leaves
blocked.  The held arm's fault is answered in place here for the first time. -/
theorem replyRecvTransferOnCore_arm_fault_inPlace (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (grant : Bool) (core : CoreId)
    (ct rt : TCB) (ep : Endpoint) (rp : Reply) (tf : ThreadFault)
    (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regMessageBody layout rf len, badge := badge }
        grant core st =
      .ok ({ results := #[] }, performReplyRecvArmFaultAnswer arm scId home st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
        len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvArmFaultAnswer arm scId home st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
        len) tid 0 =
      performReplyRecvArmFaultAnswer arm scId home st c tid rid epId ep.recvTailCode core ct.faultKind
        label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3
        ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_arm_inPlace arm
    (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge })
    st epId tid c rid IpcMessage.empty grant core ct rt ep rp hAd (by simp [IpcMessage.empty])
    hT hRO hE hS hR hEnq hRp hStash hRec
    (fun h => by rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label _ hTc hPF] at h; cases h)
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label
    { registers := Architecture.regMessageBody layout rf len, badge := badge } hTc hPF
  have hAp : ∀ X : SystemState, replyRecvAnswerCaller
        (replyRecvCallerFaultAnswer? st c label
          { registers := Architecture.regMessageBody layout rf len, badge := badge }) X c 0 =
      performFaultAnswer X c ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
        (Architecture.regMessageLength layout len) 0 := fun X => by
    rw [hAns]
    exact faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF _ _ layout rf
      (Architecture.regMessageLength layout len) 0
      (by simp only [Architecture.regMessageBody_size, Nat.min_self])
      (fun i hi => wordAt_regMessageBody layout rf len i hi)
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge })
      { registers := Architecture.regMessageBody layout rf len, badge := badge } =
      IpcMessage.empty := by rw [hAns]; rfl
  have hFF : replyRecvFaultFirst (replyRecvCallerFaultAnswer? st c label
        { registers := Architecture.regMessageBody layout rf len, badge := badge })
        (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) c =
      performFaultAnswer (arm.pop (arm.faultLeg st c tid rid) c tid scId home) c ct.faultKind label
        ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
        ct.faultX5 ct.faultX6 ct.faultX7 layout rf (Architecture.regMessageLength layout len) 0 := by
    rw [← hAp, hAns, arm.faultLeg_eq]; rfl
  have hNoA : (performFaultAnswer (arm.pop (arm.faultLeg st c tid rid) c tid scId home) c
      ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
      ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 layout rf
      (Architecture.regMessageLength layout len) 0).objects.noResizeDue := by
    rw [← hFF, hAns]
    exact (faultReplyApplyOnCore_answerGuardFrame _ c _ (arm.pop_noResizeDue (scId := scId)
      (home := home) _ c tid (arm.leg_noResizeDue st c tid rid IpcMessage.empty hNo))).2
  have hSL : ∀ Z, replyRecvStageLast (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) Z c 0 = Z :=
    fun Z => by rw [hAns]; rfl
  rw [hFF] at hEq hX
  rw [hSL] at hEq
  refine ⟨?_, ?_⟩
  · rw [replyRecvTransferOnCore_of_admits (hAd.popAdmits hT hRO)]
    unfold performReplyRecvArmFaultAnswer
    rw [hL, hEq, ReplyRecvArm.tailFast_eq]
  · obtain ⟨x', hX', e'⟩ := arm.tail_blocked _ tid rid epId ep.recvTailCode core hNoA hX
    unfold performReplyRecvArmFaultAnswer
    rw [ReplyRecvArm.tailFast_eq]
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x' hX'
      (by rw [e', hB]; exact fun h => by cases h)

/-- **The long blocking reply-receive answering a fault, over every arm**: as
`performReplyRecvArmFaultAnswer`, the reply's words past MR3 read from the
replier's buffer (`performFaultAnswerLong`) on the state the answer runs on,
before the receive's tail. -/
@[noinline] def performReplyRecvArmFaultAnswerLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (core : CoreId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  arm.tailFast (performFaultAnswerLong (arm.pop (arm.faultLeg st c tid rid) c tid scId home) c kind
    label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf len) tid rid epId tailCode core

/-- **The long blocking reply-receive answering a fault is the
specification's, over every arm**, and it stages nothing for the server. -/
theorem replyRecvTransferOnCore_arm_fault_inPlaceLong (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply) (tf : ThreadFault)
    (hAd : arm.Admits scId home st tid c rid ct rt rp) (hLen : 4 ≤ len)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st =
      .ok ({ results := #[] }, performReplyRecvArmFaultAnswerLong arm scId home st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvArmFaultAnswerLong arm scId home st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len)
        tid 0 =
      performReplyRecvArmFaultAnswerLong arm scId home st c tid rid epId ep.recvTailCode core ct.faultKind
        label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3
        ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  let msg : IpcMessage := { registers := longReplyRecvRegs rf st tid len, badge := badge }
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_arm_inPlace arm
    (replyRecvCallerFaultAnswer? st c label msg)
    st epId tid c rid IpcMessage.empty grant core ct rt ep rp hAd (by simp [IpcMessage.empty])
    hT hRO hE hS hR hEnq hRp hStash hRec
    (fun h => by rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label _ hTc hPF] at h; cases h)
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label msg hTc hPF
  have hNoL := arm.leg_noResizeDue st c tid rid IpcMessage.empty hNo
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoL
  have hW : ipcWordReadsAgree (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home)
      st :=
    ((arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoL).trans
      (arm.ipcBufferReadsAgree_leg st c tid rid IpcMessage.empty hNo)).words
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label msg) msg =
      IpcMessage.empty := by rw [hAns]; rfl
  have hFF : replyRecvFaultFirst (replyRecvCallerFaultAnswer? st c label msg)
        (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) c =
      performFaultAnswerLong (arm.pop (arm.faultLeg st c tid rid) c tid scId home) c ct.faultKind
        label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3
        ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 tid rf len := by
    rw [hAns, arm.faultLeg_eq]
    exact faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ tid rf len
      (replyWordOr_longReplyRecvRegs st _ tid rf len label hLen hW)
  have hNoA : (performFaultAnswerLong (arm.pop (arm.faultLeg st c tid rid) c tid scId home) c
      ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
      ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 tid rf len).objects.noResizeDue := by
    rw [← hFF, hAns]
    exact (faultReplyApplyOnCore_answerGuardFrame _ c _ hNoP).2
  have hSL : ∀ Z, replyRecvStageLast (replyRecvCallerFaultAnswer? st c label msg) Z c 0 = Z :=
    fun Z => by rw [hAns]; rfl
  rw [hFF] at hEq hX
  rw [hSL] at hEq
  refine ⟨?_, ?_⟩
  · rw [replyRecvTransferOnCore_of_admits (hAd.popAdmits hT hRO)]
    unfold performReplyRecvArmFaultAnswerLong
    rw [hL, hEq, ReplyRecvArm.tailFast_eq]
  · obtain ⟨x', hX', e'⟩ := arm.tail_blocked _ tid rid epId ep.recvTailCode core hNoA hX
    unfold performReplyRecvArmFaultAnswerLong
    rw [ReplyRecvArm.tailFast_eq]
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x' hX'
      (by rw [e', hB]; exact fun h => by cases h)

/-! ### The capability transfer -/

/-- **The held reply-receive that blocks, its reply leg transferring**: as
`replyRecvAnsweringOnCore_held_inPlace`, with the reply leg's transfer
answering `(summary, S2)` on the state the held pop leaves and the receive's
block admissible on `S2`. -/
theorem replyRecvOnCore_held_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint) (rp : Reply)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyHeldPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hS : ep.sendQ.head = none)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant
      (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid
        ⟨replyHeadContextCode st rid - 1⟩) = .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {rt2 : TCB}
    (hR2 : S2.objects[tid.toObjId]? = some (.tcb rt2)) (hA2 : receiveBlockAdmits rt2 = true)
    (hNo2 : S2.objects.noResizeDue)
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) (hNeTC : tid ≠ c) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore
          (removeRunnableOnCore (storeReceiveBlock (receiveReturnSchedContext true S2 tid) epId tid
            ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 c
            summary.capInfo) := by
  obtain ⟨rp', scId, sc, _, hRp', hN, _, _, _, hCode, hCRes, _, _, hNo, _, _, hLC, hFC,
    hLR, hFR, _, hPop⟩ := replyHeldPopsInPlace_pop st c tid rid msg ct hT hG
  rw [hRp] at hRp'
  cases hRp'
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc] at hXf
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st tid c tid ct ep0 rid rp msg core hSz hT hIpc hRO
    hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRecS : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  rw [← storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hPop
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hPop hXf
  generalize hP : keepDonatedSchedContextInPlace S1 tid scId = P at hPop hXf
  have hXf' : replyRecvReplyTransfer none st tid c grant P = .ok (summary, S2) := hXf
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true S2 tid hNo2
    hE2 hR2 hA2 hG2
  generalize hQ : receiveReturnSchedContext true S2 tid = Q at hE3 hR3 hG3 ⊢
  have hEp2 : Q.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE3
  have hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
      (removeRunnableOnCore (storeReceiveBlock Q epId tid ep.recvTailCode
        (SeLe4n.ReplyId.optCode (some rid))) tid core, .ok (tid, { results := #[] }, none)) := by
    unfold endpointReceiveDualWithCapsOnCore
    rw [receiveBlock_inPlace_eq Q epId ep tid rt3 (some rid) core hE3 hS hR3 hA3 hG3]
    have hSnd : (receiveRendezvousSender? Q epId).isNone = true := by
      simp [receiveRendezvousSender?, hEp2, hS]
    simp only [hSnd, ↓reduceIte]
  obtain ⟨tb, hTb, hBk⟩ := receiveBlock_receiver_blocked Q epId ep tid rt3 (some rid) core hE3 hR3
    hA3 hG3
  have hDq : rendezvousDequeuedCall (removeRunnableOnCore (storeReceiveBlock Q epId tid
      ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid = false := by
    unfold rendezvousDequeuedCall lookupTcb
    simp only [hSRes, Bool.false_eq_true, ↓reduceIte, hTb, hBk]
  have hSnd0 : receiveRendezvousSender? Q epId = none := by
    simp [receiveRendezvousSender?, hEp2, hS]
  have hNoQ : Q.objects.noResizeDue := hQ ▸ receiveReturnSchedContext_noResizeDue true S2 tid hNo2
  unfold endpointReplyRecvOnCore
  rw [endpointReplyRecvAnsweringOnCore_answerFirst_at none epId tid rid c msg grant core st
    (by simp) (Ne.symm hNeTC) hEq hPop hXf' hNo2 (by rw [hQ, hSnd0]; simp)
    (fun _ => .inr ⟨by rw [hQ]; unfold receiveCapRequest; rw [hSnd0], fun s0 E hE => ?_⟩)]
  · simp only [hRecS, Option.getD_some, hQ, hRecv]
    simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff, replyRecvAnswerCaller]
  · simp only [hRecS, Option.getD_some, hQ, hRecv] at hE
    simp [replyRecvPostReceiveDonation, hDq, applyReceiveLegPipHandoff] at hE
    obtain ⟨-, rfl⟩ := hE
    exact ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core
      (removeRunnableOnCore_noResizeDue _ _ _ (storeReceiveBlock_noResizeDue _ _ _ _ _ hNoQ))).trans
      ((ipcBufferReadsAgree_removeRunnableOnCore _ tid core).trans
        ((ipcBufferReadsAgree_storeReceiveBlock Q epId tid _ _ hNoQ).trans
          (hQ ▸ ipcBufferReadsAgree_receiveReturnSchedContext true S2 tid hNo2)))).words

/-- **The blocking reply-receive whose reply leg transfers, over every arm**:
with the reply leg's transfer answering `(summary, S2)` on the state the arm's
pop leaves and the receive's block admissible on `S2`, the composite is the
arm's tail on `S2` and the caller staged with the transfer's report. -/
theorem replyRecvOnCore_arm_transfer (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (grant : Bool) (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hS : ep.sendQ.head = none)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant (arm.pop (arm.leg st c tid rid msg) c tid scId home) =
      .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {rt2 : TCB}
    (hR2 : S2.objects[tid.toObjId]? = some (.tcb rt2)) (hA2 : receiveBlockAdmits rt2 = true)
    (hNo2 : S2.objects.noResizeDue)
    (hG2 : receiveBlocksInPlace S2 epId tid ep.receiveQ.tail (some rid) = true) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageDeliveredMessage
        (arm.tail S2 tid rid epId ep.recvTailCode core) c summary.capInfo) := by
  have hNeTC := (hAd.facts hT).1
  cases arm with
  | rendezvous =>
    obtain ⟨⟨ep0, hIpc⟩, hG, -, -, -⟩ := hAd
    exact replyRecvOnCore_blocks_transfer st epId tid c rid msg grant core ct ep0 ep hSz hT hIpc
      hRO hG hS hXf hE2 hR2 hA2 hNo2 hG2 hNeTC
  | donated =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, -, rfl, rfl⟩ := hAd
    exact replyRecvOnCore_donated_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT hIpc
      hRO hSRes hG hS hRp hXf hE2 hR2 hA2 hNo2 hG2 hNeTC
  | held =>
    obtain ⟨⟨ep0, hIpc⟩, hSRes, hG, -, -, rfl⟩ := hAd
    exact replyRecvOnCore_held_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT hIpc
      hRO hSRes hG hS hRp hXf hE2 hR2 hA2 hNo2 hG2 hNeTC
  | unheld =>
    obtain ⟨⟨ep0, hIpc⟩, hG, -, -, rfl, rfl⟩ := hAd
    exact replyRecvOnCore_unheld_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT hIpc
      hRO hG hS hRp hXf hE2 hR2 hA2 hNo2 hG2 hNeTC
  | unlinked =>
    obtain ⟨⟨ep0, hIpc⟩, hG, -, -⟩ := hAd
    exact replyRecvOnCore_unlinked_transfer st epId tid c rid msg grant core ct ep0 ep rp hSz hT
      hIpc hRO hG hS hRp hXf hE2 hR2 hA2 hNo2 hG2 hNeTC

/-- **The reply leg and the arm's pop carry the receive's guard**: on the state
they leave, the endpoint is as it was, the server may block on it and its block
writes in place, each read on the pre-state.  Per arm, the arm's own carry
(`storeReplyRendezvous_receiveGuard`, `popDonationSettled_receiveGuard`,
`keepHeldPop_receiveGuard`, `popUnheldSettled_receiveGuard`,
`storeReplyLeg_receiveGuard`). -/
theorem ReplyRecvArm.receiveGuard (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage)
    (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    (arm.pop (arm.leg st c tid rid msg) c tid scId home).objects[epId]? = some (.endpoint ep) ∧
      (∃ rt1, (arm.pop (arm.leg st c tid rid msg) c tid scId home).objects[tid.toObjId]? =
          some (.tcb rt1) ∧ receiveBlockAdmits rt1 = true ∧
          rt1.boundNotificationCode = rt.boundNotificationCode) ∧
      receiveBlocksInPlace (arm.pop (arm.leg st c tid rid msg) c tid scId home) epId tid ep.receiveQ.tail
        (some rid) = true := by
  cases arm with
  | rendezvous =>
    obtain ⟨-, hG, hNe, hA, hFree⟩ := hAd
    rw [Reply.consumedIsFree_eq] at hFree
    have hNo := replyWakesInPlace_noResizeDue hG
    have hFC : st.objects.findsInPlace c.toObjId = true := by
      simp only [replyWakesInPlace, Bool.and_eq_true] at hG
      exact hG.1.1.1.2
    exact storeReplyRendezvous_receiveGuard st c tid rid msg ct rp epId ep rt hNo hT hFC hRp hNe
      hE hR hA hEnq hFree hStash hRec
  | donated =>
    obtain ⟨-, hSRes, hG, hA, rfl, rfl⟩ := hAd
    obtain ⟨rp', scId', sc, hRp', hN, hScO, hHead, hBelow, hCode, -, hNe', hNo, -, hFC, -⟩ :=
      replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId' := by
      rw [hCode]; rfl
    show (popDonationSettledInPlace (storeReplyRendezvous st c tid rid msg) c tid _ _).objects[epId]? =
      _ ∧ _
    rw [hSc]
    exact popDonationSettled_receiveGuard st c tid rid msg ct rp epId ep rt scId' sc _ hNo hT hFC
      hRp hN hScO hHead hBelow (fun e => hNe' e.symm) hE hR hA hEnq hStash hRec
  | held =>
    obtain ⟨-, -, hG, hOwn, hA, rfl⟩ := hAd
    obtain ⟨rp', scId', sc, _, hRp', hN, hScO, hHead, hBelow, hCode, -, -, hNe', hNo, -, -, -, hFC,
      -⟩ := replyHeldPopsInPlace_pop st c tid rid msg ct hT hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId' := by
      rw [hCode]; rfl
    show (keepDonatedSchedContextInPlace (storeReplyRendezvous st c tid rid msg) tid _).objects[epId]?
      = _ ∧ _
    rw [hSc]
    exact keepHeldPop_receiveGuard st c tid rid msg ct rp epId ep rt scId' sc hNo hT hFC hRp hN hScO
      hHead hBelow (fun e => hNe' e.symm) hE hR hOwn hA hEnq hStash hRec
  | unheld =>
    obtain ⟨-, hG, hNe, hA, rfl, rfl⟩ := hAd
    obtain ⟨rp', scId', hRp', hN, hCode, -, hNo, -, hFC, -⟩ :=
      replyUnheldPopsInPlace_pop st c rid msg ct hT hG
    obtain ⟨rp'', scId'', sc, hRp'', hN', hScO, hHead, hBelow⟩ := replyUnheldPopsInPlace_stack st c rid hG
    rw [hRp] at hRp' hRp''
    cases hRp'
    cases hRp''
    rw [hN] at hN'
    cases hN'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId' := by
      rw [hCode]; rfl
    show (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
      (storeReplyLeg st c rid msg) c _) _ _).objects[epId]? = _ ∧ _
    rw [hSc]
    exact popUnheldSettled_receiveGuard st c tid rid msg ct rp epId ep rt scId' sc _ hNo hT hFC hRp
      hN hScO hHead hBelow hNe hE hR hA hEnq hStash hRec
  | unlinked =>
    obtain ⟨-, hG, hNe, hA⟩ := hAd
    have hW : replyWakesInPlace st c ct rid = true := hG
    exact storeReplyLeg_receiveGuard st c tid rid msg ct rp epId ep rt
      (replyWakesInPlace_noResizeDue hW) hT (replyUnlinkedInPlace_findsCaller hG) hRp hNe hE hR hA
      hEnq (replyUnlinkedInPlace_consumedFree hG hRp) hStash hRec

/-! ### The capability answer -/

/-- **The receive tail stages the caller's held reply and the transfer's report
as the caller's frame**, the server it blocks staging nothing: on a state `Y`
the reply's transfer leaves, the receive's block admissible on `Y` with the
caller holding the reply. -/
theorem ReplyRecvArm.tail_staged (arm : ReplyRecvArm) (Y : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (ep : Endpoint) (core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hE2 : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })).objects[epId]? =
        some (.endpoint ep)) {rt2 : TCB}
    (hR2 : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })).objects[tid.toObjId]? =
        some (.tcb rt2))
    (hA2 : receiveBlockAdmits rt2 = true)
    (hG2 : receiveBlocksInPlace (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })) epId tid
        ep.receiveQ.tail (some rid) = true) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (arm.tail (Y.mapTcbInPlace c (holdMessage
          { registers := Architecture.regMessageBody layout rf len, badge := badge })) tid rid epId
          ep.recvTailCode core) c capInfo) tid 0 =
      deliverReplyRecvCapsFrame capInfo (arm.tailFast Y tid rid epId ep.recvTailCode core) c layout
        rf len badge := by
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true _ tid
    ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNo) hE2 hR2 hA2 hG2
  obtain ⟨t, hT0, hBk⟩ := receiveBlock_receiver_blocked _ epId ep tid rt3 (some rid) core hE3 hR3
    hA3 hG3
  have hT1 : (ReplyRecvArm.blocked (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regMessageBody layout rf len, badge := badge })) tid rid epId
      ep.recvTailCode core).getTcb? tid = some t := hT0
  have h3 := ReplyRecvArm.blocked_noResizeDue Y tid rid epId ep.recvTailCode core hNo
  rw [ReplyRecvArm.blocked_msg c _ Y tid rid epId _ core hNo (fun e => hNe e.symm),
    SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hT1
  obtain ⟨x1, hX1, e1⟩ := arm.desched_ipcStateCarried _ tid tid t hT1
  obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core
    (arm.desched_noResizeDue _ tid h3) tid x1 hX1
  have hX' : (arm.tailFast Y tid rid epId ep.recvTailCode core).getTcb? tid = some x := by
    rw [ReplyRecvArm.tailFast_eq]; exact hX
  rw [arm.tail_msg c _ Y tid rid epId _ core hNo (fun e => hNe e.symm),
    stageDeliveredMessage_holdMessage_caps _ _ _ _ (arm.tail_noResizeDue Y tid rid epId _ core hNo)
      (by rw [Architecture.regMessageBody_size]; exact hSz4),
    returnFrameOfMessage_regMessageBody_capsOpt, ← ReplyRecvArm.tailFast_eq]
  exact stageDeliveredMessage_writeDeliveredFrameIfReady_blocked
    (arm.tailFast Y tid rid epId ep.recvTailCode core) c tid _ _ 0 hCT x hX'
    (by rw [hEq, e1, hBk]; exact fun h => by cases h)

/-- **The blocking reply-receive whose reply leg transfers, delivered, over
every arm**: the arm's reply leg and pop, the transfer in place on no endpoint,
the arm's tail, then the caller's frame with the transfer's report.  The held
arm's capability answer is in place here for the first time. -/
@[noinline] def performReplyRecvArmCapsDelivered (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid scId home
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverReplyRecvCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (arm.tailFast
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
        tid rid epId tailCode core)
      c layout rf len badge

/-- **The blocking reply-receive whose reply leg transfers, delivered, over
every arm**: under the arm's guard, a granting replier whose frame asks for
`count` capabilities and a reply of at most four words, the checked arm's
result is `performReplyRecvArmCapsDelivered`. -/
theorem replyRecvOnCore_arm_capsDelivered (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (core : CoreId) (ct rt : TCB) (ep : Endpoint) (rp : Reply)
    (stcb : TCB) (count : Nat)
    (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCapsDelivered arm scId home st c tid rid epId ep.recvTailCode layout rf len
        badge core stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2]
        ct.ipcBuffer ct.spaceCells[0]) := by
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  generalize hMsg : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = msg
  obtain ⟨hE1, ⟨rt1, hR1, hA1, -⟩, hG1⟩ := arm.receiveGuard st epId tid c rid msg ct rt ep rp hAd
    hT hE hR hEnq hRp hStash hRec
  have hNoX := arm.legReady_noResizeDue st c tid rid hNo
  have hP1 : arm.pop (arm.leg st c tid rid msg) c tid scId home =
      (arm.pop (arm.legReady st c tid rid) c tid scId home).mapTcbInPlace c (holdMessage msg) := by
    rw [arm.leg_eq_hold st c tid rid msg hNo]
    exact arm.pop_msg (scId := scId) (home := home) c id _ id _ c tid hNoX (fun e => hNe e.symm)
  have hAP := (arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoX).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoX
  generalize hX : arm.pop (arm.legReady st c tid rid) c tid scId home = X at hP1 hNoP hAP
  rw [hP1] at hE1 hR1 hG1
  obtain ⟨s, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAP)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hHT).1
  obtain ⟨hE2, ⟨rt2, hR2, hA2, -⟩, hG2⟩ := receiveGuard_of_transferFrame hFr hE1 hR1 hA1 hG1
  have hXf : replyTransferCaps st tid c true (arm.pop (arm.leg st c tid rid msg) c tid scId home) =
      .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hP1, hHT]
  rw [replyRecvOnCore_arm_transfer arm st epId tid c rid msg true core ct rt ep rp hAd (hMsg ▸ hSz)
    hT hRO hS hRp hXf hE2 hR2 hA2 ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY) hG2]
  dsimp only
  subst hMsg
  simp only [CapTransferSummary.capInfo_empty]
  rw [arm.tail_staged Y1 c tid rid epId ep core layout rf len badge s.capInfo hNoY hNe hSz4 hE2 hR2
    hA2 hG2]
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverReplyRecvCapsFrame i (arm.tailFast Y tid rid epId ep.recvTailCode core) c
      layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hK
  unfold performReplyRecvArmCapsDelivered
  rw [hX]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState))) hK.symm

/-- **The long blocking reply-receive whose reply leg transfers, delivered,
over every arm**: as `performReplyRecvArmCapsDelivered`, with the long frame. -/
@[noinline] def performReplyRecvArmCapsDeliveredLong (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (core : CoreId)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid scId home
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverLongReplyRecvCapsFrame
      (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (arm.tailFast
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
        tid rid epId tailCode core)
      c rf len tid badge

/-- **The long blocking reply-receive whose reply leg transfers, delivered,
over every arm**: as `replyRecvOnCore_arm_capsDelivered`, for a message of
`len` words, more than four, read in the replier's registers and buffer. -/
theorem replyRecvOnCore_arm_capsDeliveredLong (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (core : CoreId)
    (ct rt : TCB) (ep : Endpoint) (rp : Reply) (stcb : TCB) (count : Nat)
    (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hLen : 5 ≤ len) (hSz : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCapsDeliveredLong arm scId home st c tid rid epId ep.recvTailCode rf len
        badge core stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2]
        ct.ipcBuffer ct.spaceCells[0]) := by
  obtain ⟨hNe, hNo⟩ := hAd.facts hT
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  generalize hMsg : ({ registers := longReplyRecvRegs rf st tid len, badge := badge } :
    IpcMessage) = msg
  obtain ⟨hE1, ⟨rt1, hR1, hA1, -⟩, hG1⟩ := arm.receiveGuard st epId tid c rid msg ct rt ep rp hAd
    hT hE hR hEnq hRp hStash hRec
  have hNoX := arm.legReady_noResizeDue st c tid rid hNo
  have hP1 : arm.pop (arm.leg st c tid rid msg) c tid scId home =
      (arm.pop (arm.legReady st c tid rid) c tid scId home).mapTcbInPlace c (holdMessage msg) := by
    rw [arm.leg_eq_hold st c tid rid msg hNo]
    exact arm.pop_msg (scId := scId) (home := home) c id _ id _ c tid hNoX (fun e => hNe e.symm)
  have hAP := (arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoX).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoX
  generalize hX : arm.pop (arm.legReady st c tid rid) c tid scId home = X at hP1 hNoP hAP
  rw [hP1] at hE1 hR1 hG1
  obtain ⟨s, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAP)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hHT).1
  obtain ⟨hE2, ⟨rt2, hR2, hA2, -⟩, hG2⟩ := receiveGuard_of_transferFrame hFr hE1 hR1 hA1 hG1
  have hXf : replyTransferCaps st tid c true (arm.pop (arm.leg st c tid rid msg) c tid scId home) =
      .ok (s, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hP1, hHT]
  have hNoY' : (Y1.mapTcbInPlace c (holdMessage msg)).objects.noResizeDue :=
    (SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY
  rw [replyRecvOnCore_arm_transfer arm st epId tid c rid msg true core ct rt ep rp hAd (hMsg ▸ hSz)
    hT hRO hS hRp hXf hE2 hR2 hA2 hNoY' hG2]
  dsimp only
  subst hMsg
  simp only [CapTransferSummary.capInfo_empty]
  obtain ⟨hE3, ⟨rt3, hR3, hA3⟩, hG3⟩ := receiveReturnSchedContext_receiveGuard true _ tid hNoY'
    hE2 hR2 hA2 hG2
  obtain ⟨t2, hT2, hB2⟩ := receiveBlock_receiver_blocked _ epId ep tid rt3 (some rid) core hE3 hR3
    hA3 hG3
  have hWY := ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoP hT1
  rw [arm.tail_stagedLong Y1 st c tid rid epId ep.recvTailCode core rf len badge s.capInfo hNoY hNe
    hLen ((arm.ipcBufferReadsAgree_tail Y1 tid rid epId ep.recvTailCode core hNoY).words.trans
      (hWY.trans hAP.words)) ⟨t2, hT2, hB2⟩, ← ReplyRecvArm.tailFast_eq]
  have hK := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => deliverLongReplyRecvCapsFrame i (arm.tailFast Y tid rid epId ep.recvTailCode core) c
      rf len tid badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hK
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hK
  unfold performReplyRecvArmCapsDeliveredLong
  rw [hX]
  exact congrArg (fun Z => (.ok ((), Z) : Except KernelError (Unit × SystemState))) hK.symm

/-- **The blocking reply-receive of a message in registers, delivered, over
every arm**: `replyRecvOnCore_arm_delivered` for the reply the replier's frame
holds, its result `performReplyRecvArmDelivered`. -/
theorem replyRecvOnCore_arm_deliveredRegs (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (grant : Bool) (core : CoreId) (ct rt : TCB) (ep : Endpoint)
    (rp : Reply) (hAd : arm.Admits scId home st tid c rid ct rt rp)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt))
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true)
    (hInert : replyTransferInert st tid ct grant = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmDelivered arm scId home st c tid rid epId ep.recvTailCode layout
        rf len badge core) := by
  have hSz4' : (Architecture.regMessageBody layout rf len).size ≤ 4 := by
    rw [Architecture.regMessageBody_size]; exact hSz4
  rw [replyRecvOnCore_arm_delivered arm st epId tid c rid _ grant core ct rt ep rp hAd
    (by show ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters
        unfold maxMessageRegisters; omega) hSz4' hT hRO hE hS hR hEnq hRp hStash hRec hInert,
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

end SeLe4n.Kernel
