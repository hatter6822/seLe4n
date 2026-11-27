/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReceiveAnswerCommute

/-!
# The `.replyRecv` tail: what the stage reads, and the post-receive donation

WS-SX SX31.  Answering the replied-to caller before the receive leg instead of
after it needs two facts about the steps between: they commute with the
answer's slot write (`ReceiveAnswerCommute`, extended here to the post-receive
donation, the holder's deschedule and the priority hand-off), and they leave
what the stage reads off the caller -- its IPC state and its pending message --
as it was (`answerReadsKept`).  The second is what lets the stage computed on
the receive's entry state be the stage computed on the tail's result.

Every lemma here assumes only that no resize of the object table is due: each
store is at a present key, where it is a write in its slot.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- What the stage reads off the answered thread: its IPC state and its message. -/
def tcbAnswerReads (t : TCB) : ThreadIpcState × Option IpcMessage := (t.ipcState, t.pendingMessage)

/-- The answered thread's IPC state and message, read off an object. -/
def answerReadsOf : Option KernelObject → Option (ThreadIpcState × Option IpcMessage)
  | some (.tcb t) => some (tcbAnswerReads t)
  | _ => none

/-- **A step that keeps what the stage reads off `c`.** -/
def answerReadsKept (c : SeLe4n.ThreadId) (X Y : SystemState) : Prop :=
  (Y.getTcb? c).map tcbAnswerReads = (X.getTcb? c).map tcbAnswerReads

namespace answerReadsKept
variable {c : SeLe4n.ThreadId}
theorem refl (X : SystemState) : answerReadsKept c X X := rfl
theorem trans {X Y W : SystemState} (h1 : answerReadsKept c X Y) (h2 : answerReadsKept c Y W) :
    answerReadsKept c X W := Eq.trans h2 h1
theorem of_eq {X Y : SystemState} (h : Y = X) : answerReadsKept c X Y := h ▸ rfl
end answerReadsKept

theorem getTcb?_map_answerReads (X : SystemState) (c : SeLe4n.ThreadId) :
    (X.getTcb? c).map tcbAnswerReads = answerReadsOf (X.objects[c.toObjId]?) := by
  unfold SystemState.getTcb?
  cases X.objects[c.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem answerReadsKept_of_objects {c : SeLe4n.ThreadId} {X Y : SystemState}
    (h : answerReadsOf (Y.objects[c.toObjId]?) = answerReadsOf (X.objects[c.toObjId]?)) :
    answerReadsKept c X Y := by
  unfold answerReadsKept; rw [getTcb?_map_answerReads, getTcb?_map_answerReads, h]

theorem answerReadsKept_iff_objects {c : SeLe4n.ThreadId} {X Y : SystemState} :
    answerReadsKept c X Y ↔ answerReadsOf (Y.objects[c.toObjId]?) = answerReadsOf (X.objects[c.toObjId]?) := by
  unfold answerReadsKept; rw [getTcb?_map_answerReads, getTcb?_map_answerReads]

theorem mapTcbInPlace_answerReadsKept (c x : SeLe4n.ThreadId) (X : SystemState) (g : TCB → TCB)
    (hg : x = c → ∀ t, tcbAnswerReads (g t) = tcbAnswerReads t) :
    answerReadsKept c X (X.mapTcbInPlace x g) := by
  unfold answerReadsKept
  rw [SystemState.getTcb?_mapTcbInPlace]
  split
  · next h => cases X.getTcb? c <;> simp [hg h]
  · rfl

theorem updateTcb_answerReadsKept (c x : SeLe4n.ThreadId) (X : SystemState) (g : TCB → TCB)
    (hNo : X.objects.noResizeDue) (hg : x = c → ∀ t, tcbAnswerReads (g t) = tcbAnswerReads t) :
    answerReadsKept c X (X.updateTcb x g) := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
  exact mapTcbInPlace_answerReadsKept c x X g hg

theorem objects_insert_present (X : SystemState) (k : SeLe4n.ObjId) (o0 o : KernelObject)
    (hk : X.objects[k]? = some o0) (hNo : X.objects.noResizeDue) (y : SeLe4n.ObjId) :
    (X.objects.insert k o)[y]? = if k == y then some o else X.objects[y]? := by
  have hg : X.objects.get? k = some o0 := by simpa only [RHTable_getElem?_eq_get?] using hk
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hg), RHTable.get?_mapValueAt]
  split
  · next h => have := beq_iff_eq.mp h; subst this; rw [hg]; rfl
  · rfl

theorem insert_answerReadsKept (c : SeLe4n.ThreadId) (X : SystemState) (k : SeLe4n.ObjId)
    (o0 o : KernelObject) (hk : X.objects[k]? = some o0) (hNo : X.objects.noResizeDue)
    (hw : k = c.toObjId → answerReadsOf (some o) = answerReadsOf (some o0)) :
    answerReadsKept c X { X with objects := X.objects.insert k o } := by
  apply answerReadsKept_of_objects
  show answerReadsOf ((X.objects.insert k o)[c.toObjId]?) = _
  rw [objects_insert_present X k o0 o hk hNo]
  split
  · next he => have := beq_iff_eq.mp he; rw [hw this, ← hk, this]
  · rfl

theorem storeObject_answerReadsKept (c : SeLe4n.ThreadId) (X Y : SystemState) (k : SeLe4n.ObjId)
    (o0 o : KernelObject) (hk : X.objects[k]? = some o0) (hNo : X.objects.noResizeDue)
    (hw : k = c.toObjId → answerReadsOf (some o) = answerReadsOf (some o0))
    (h : storeObject k o X = .ok ((), Y)) : answerReadsKept c X Y := by
  unfold storeObject at h; cases h
  exact insert_answerReadsKept c X k o0 o hk hNo hw

theorem modifyTcb_answerReadsKept (c x : SeLe4n.ThreadId) (X Y : SystemState) (g : TCB → TCB)
    (hNo : X.objects.noResizeDue) (hg : x = c → ∀ t, tcbAnswerReads (g t) = tcbAnswerReads t)
    (h : modifyTcb X x g = .ok Y) : answerReadsKept c X Y := by
  by_cases hR : x.isReserved = true
  · unfold modifyTcb lookupTcb at h; simp only [hR, ↓reduceIte] at h; cases h
  · have hR' : x.isReserved = false := by simpa using hR
    cases hT : X.getTcb? x with
    | none => unfold modifyTcb lookupTcb at h; simp only [hR', hT, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | some tcb =>
      rw [modifyTcb_eq_updateTcb g hR' hT (storeLeavesIndexAndTypes_tcb_of_getTcb? hT)] at h
      cases h
      exact updateTcb_answerReadsKept c x X g hNo hg

theorem answerReadsKept_of_agreeOffRunLinks {c : SeLe4n.ThreadId} {X Y : SystemState}
    (h : Y.objectsAgreeOffRunLinks X) : answerReadsKept c X Y := by
  apply answerReadsKept_of_objects
  have e := h c.toObjId
  revert e
  cases Y.objects[c.toObjId]? with
  | none => cases X.objects[c.toObjId]? <;> simp
  | some o' =>
    cases X.objects[c.toObjId]? with
    | none => simp
    | some o =>
      intro e
      simp only [Option.map_some, Option.some.injEq] at e
      cases o' <;> cases o <;> simp_all [KernelObject.withoutRunLinks, answerReadsOf, tcbAnswerReads]
      exact ⟨TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState e,
        TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingMessage e⟩


theorem storeTcbQueueLinks_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState) (t : SeLe4n.ThreadId)
    (p : Option SeLe4n.ThreadId) (pp : Option QueuePPrev) (n : Option SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) (h : storeTcbQueueLinks Z t p pp n = .ok Z') : answerReadsKept c Z Z' :=
  modifyTcb_answerReadsKept c t Z Z' (fun tcb => tcbWithQueueLinks tcb p pp n) hNo (fun _ _ => rfl) h

theorem endpointQueuePopHead_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState) (k : SeLe4n.ObjId)
    (isRecv : Bool) (t : SeLe4n.ThreadId) (tcb : TCB) (Z' : SystemState) (hNo : Z.objects.noResizeDue)
    (h : endpointQueuePopHead k isRecv Z = .ok (t, tcb, Z')) : answerReadsKept c Z Z' := by
  unfold endpointQueuePopHead at h
  cases hO : Z.getObject? k with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o with
    | endpoint ep =>
      have hk : Z.objects[k]? = some (.endpoint ep) := hO
      have hL : ∀ e : Endpoint, storeLeavesIndexAndTypes Z k (KernelObject.endpoint e).objectType = true :=
        fun e => by unfold storeLeavesIndexAndTypes storeKeepsKind; rw [hk]; rfl
      have hE : ∀ e : Endpoint, answerReadsKept c Z { Z with objects := Z.objects.insert k (.endpoint e) } :=
        fun e => insert_answerReadsKept c Z k _ (.endpoint e) hk hNo (fun _ => rfl)
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · rw [storeObject_eq_of_leaves (hL _)] at h
          have hNo1 := fun e : Endpoint => insert_present_noResizeDue Z k _ (.endpoint e) hk hNo
          dsimp only at h
          split at h
          · cases h
          · rename_i Zb hZb
            split at h
            · cases h
            · rename_i Zc hZc
              cases h
              have hNoB : Zb.objects.noResizeDue := by
                split at hZb
                · cases hZb; exact hNo1 _
                · split at hZb
                  · cases hZb
                  · exact storeTcbQueueLinks_noResizeDue' _ _ _ _ _ _ (hNo1 _) hZb
              refine answerReadsKept.trans ?_ (storeTcbQueueLinks_answerReadsKept c _ _ _ _ _ _ hNoB hZc)
              split at hZb
              · cases hZb; exact hE _
              · split at hZb
                · cases hZb
                · exact (hE _).trans (storeTcbQueueLinks_answerReadsKept c _ _ _ _ _ _ (hNo1 _) hZb)
    | _ => cases h

theorem ne_toObjId {c x : SeLe4n.ThreadId} (h : x ≠ c) : x.toObjId = c.toObjId → False :=
  fun e => h (SeLe4n.ThreadId.toObjId_injective _ _ e)

theorem storeTcbIpcStateAndMessage_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (t : SeLe4n.ThreadId) (s : ThreadIpcState) (m : Option IpcMessage) (hNo : Z.objects.noResizeDue)
    (hc : t ≠ c) (h : storeTcbIpcStateAndMessage Z t s m = .ok Z') : answerReadsKept c Z Z' := by
  unfold storeTcbIpcStateAndMessage at h
  exact modifyTcb_answerReadsKept c t Z Z' _ hNo (fun e => absurd e hc) h

theorem linkReply_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState) (rid : SeLe4n.ReplyId)
    (x : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) (h : SystemState.linkReply rid x Z = .ok ((), Z')) :
    answerReadsKept c Z Z' := by
  unfold SystemState.linkReply at h
  cases hR : Z.getReply? rid with
  | none => rw [hR] at h; cases h
  | some y =>
    rw [hR] at h
    dsimp only at h
    split at h
    · exact storeObject_answerReadsKept c Z Z' _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR)
        hNo (by intro; rfl) h
    · cases h

theorem linkCallerReply_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState) (x : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : Z.objects.noResizeDue) (hc : x ≠ c)
    (h : SystemState.linkCallerReply x rid Z = .ok ((), Z')) : answerReadsKept c Z Z' := by
  unfold SystemState.linkCallerReply at h
  cases hL : SystemState.linkReply rid x Z with
  | error e => rw [hL] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, Za⟩ := p
    rw [hL] at h
    have hNo1 := linkReply_noResizeDue Z Za rid x hNo hL
    refine (linkReply_answerReadsKept c Z Za rid x hNo hL).trans ?_
    dsimp only at h
    cases hT : Za.getTcb? x with
    | none => rw [hT] at h; cases h
    | some tcb =>
      rw [hT] at h
      dsimp only at h
      split at h
      · exact storeObject_answerReadsKept c Za Z' _ _ _ ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
          hNo1 (fun e => absurd e (ne_toObjId hc)) h
      · cases h

theorem linkReplyWaiter_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState) (w s : SeLe4n.ThreadId) :
    answerReadsKept c Z (Z.linkReplyWaiter w s) :=
  answerReadsKept_of_agreeOffRunLinks (SystemState.linkReplyWaiter_objectsAgreeOffRunLinks Z w s)

theorem removeRunnableOnCore_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState)
    (t : SeLe4n.ThreadId) (k : CoreId) : answerReadsKept c Z (removeRunnableOnCore Z t k) :=
  answerReadsKept_of_agreeOffRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks Z t k)

theorem enqueueRunnableOnCore_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState) (k : CoreId)
    (t : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) (hc : t ≠ c) :
    answerReadsKept c Z (enqueueRunnableOnCore Z k t) := by
  unfold enqueueRunnableOnCore
  cases hW : Z.getTcbWitnessed? t with
  | none => exact .refl _
  | some p =>
    obtain ⟨tcb, hT⟩ := p
    dsimp only
    split
    · exact .refl _
    · exact (insert_answerReadsKept c Z t.toObjId _ _ ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hNo
        (fun e => absurd e (ne_toObjId hc))).trans
        (answerReadsKept_of_agreeOffRunLinks (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks _ _ _ _))

theorem wakeThread_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState) (t : SeLe4n.ThreadId)
    (k : CoreId) (hNo : Z.objects.noResizeDue) (hc : t ≠ c) :
    answerReadsKept c Z (wakeThread Z t k).1 :=
  enqueueRunnableOnCore_answerReadsKept c Z _ t hNo hc

theorem tcbStore_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState) (x : SeLe4n.ThreadId) (t v : TCB)
    (hL : lookupTcb Z x = some t) (hNo : Z.objects.noResizeDue) (hv : tcbAnswerReads v = tcbAnswerReads t)
    (h : storeObject x.toObjId (.tcb v) Z = .ok ((), Z')) : answerReadsKept c Z Z' :=
  storeObject_answerReadsKept c Z Z' _ (.tcb t) _
    ((SystemState.getTcb?_eq_some_iff _ _ _).mp (getTcb?_of_lookupTcb _ _ _ hL)) hNo
    (fun _ => by simp only [answerReadsOf, hv]) h

theorem replyStore_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState) (rid : SeLe4n.ReplyId)
    (g : Reply → Reply) (hNo : Z.objects.noResizeDue)
    (h : (match Z.getReply? rid with
      | some x => match storeObject rid.toObjId (.reply (g x)) Z with
        | Except.error e => Except.error e
        | Except.ok ((), st') => Except.ok st'
      | none => (Except.error KernelError.objectNotFound : Except KernelError SystemState)) = .ok Z') :
    answerReadsKept c Z Z' := by
  cases hR : Z.getReply? rid with
  | none => rw [hR] at h; cases h
  | some x =>
    rw [hR] at h
    dsimp only at h
    cases hS : storeObject rid.toObjId (.reply (g x)) Z with
    | error e => rw [hS] at h; cases h
    | ok p =>
      obtain ⟨⟨⟩, Za⟩ := p
      rw [hS] at h; cases h
      exact storeObject_answerReadsKept c Z _ _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hNo
        (by intro; rfl) hS

theorem storeDonationHeadClear_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (rid? : Option SeLe4n.ReplyId) (hNo : Z.objects.noResizeDue)
    (h : storeDonationHeadClear rid? Z = .ok Z') : answerReadsKept c Z Z' := by
  rcases rid? with _ | rid
  · cases h; exact .refl _
  · exact replyStore_answerReadsKept c Z Z' rid _ hNo h

theorem storeReplyReHead_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (scId : SeLe4n.SchedContextId) (rid? : Option SeLe4n.ReplyId) (hNo : Z.objects.noResizeDue)
    (h : storeReplyReHead scId rid? Z = .ok Z') : answerReadsKept c Z Z' := by
  rcases rid? with _ | rid
  · cases h; exact .refl _
  · exact replyStore_answerReadsKept c Z Z' rid _ hNo h

theorem storeDonationHeadPop_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (scId : SeLe4n.SchedContextId) (head? : Option (SeLe4n.ReplyId × Reply)) (hNo : Z.objects.noResizeDue)
    (h : storeDonationHeadPop scId head? Z = .ok Z') : answerReadsKept c Z Z' := by
  rcases head? with _ | ⟨rid, x⟩
  · cases h; exact .refl _
  · simp only [storeDonationHeadPop] at h
    cases h1 : storeDonationHeadClear (some rid) Z with
    | error e => rw [h1] at h; cases h
    | ok Za =>
      rw [h1] at h
      exact (storeDonationHeadClear_answerReadsKept c Z Za _ hNo h1).trans
        (storeReplyReHead_answerReadsKept c Za Z' scId _ (storeDonationHeadClear_noResizeDue _ _ _ hNo h1) h)

theorem keepDonatedSchedContext_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (n : Option SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue)
    (h : keepDonatedSchedContext Z holder scId n = .ok Z') : answerReadsKept c Z Z' := by
  unfold keepDonatedSchedContext at h
  cases hS : Z.getSchedContext? scId with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hH : donationHeadOf? Z scId sc with
        | error e => rw [hH] at h; cases h
        | ok head? =>
          rw [hH] at h
          dsimp only at h
          rw [storeObject_eq_of_leaves (storeLeaves_schedContext hS _)] at h
          have hNo1 := insert_present_noResizeDue Z _ _
            (.schedContext (donationSeverSchedContext sc (head?.bind fun p => p.snd.prev)))
            (objects_of_getSchedContext? hS) hNo
          have hF1 := insert_answerReadsKept c Z _ _
            (.schedContext (donationSeverSchedContext sc (head?.bind fun p => p.snd.prev)))
            (objects_of_getSchedContext? hS) hNo (fun _ => rfl)
          dsimp only at h
          cases hP : storeDonationHeadPop scId head? _ with
          | error e => rw [hP] at h; cases h
          | ok Zb =>
            rw [hP] at h
            have hNo2 := storeDonationHeadPop_noResizeDue _ _ scId head? hNo1 hP
            have hF2 := hF1.trans (storeDonationHeadPop_answerReadsKept c _ _ scId head? hNo1 hP)
            dsimp only at h
            cases hL : lookupTcb Zb holder with
            | none => rw [hL] at h; cases h
            | some ht =>
              rw [hL] at h
              dsimp only at h
              split at h
              · cases h
              · cases hC : storeObject holder.toObjId _ Zb with
                | error e => rw [hC] at h; cases h
                | ok p =>
                  obtain ⟨⟨⟩, Zc⟩ := p
                  rw [hC] at h
                  cases h
                  exact hF2.trans (tcbStore_answerReadsKept c _ _ _ _ _ hL hNo2 (by rfl) hC)

theorem returnDonatedSchedContext_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (server : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (n : Option SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue)
    (h : returnDonatedSchedContext Z server scId owner n = .ok Z') : answerReadsKept c Z Z' := by
  unfold returnDonatedSchedContext at h
  cases hS : Z.getSchedContext? scId with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases hH : donationHeadOf? Z scId sc with
          | error e => rw [hH] at h; cases h
          | ok head? =>
            rw [hH] at h
            dsimp only at h
            rw [storeObject_eq_of_leaves (storeLeaves_schedContext hS _)] at h
            have hNo1 := insert_present_noResizeDue Z _ _
              (.schedContext (donationReturnSchedContext sc owner (head?.bind fun p => p.snd.prev)))
              (objects_of_getSchedContext? hS) hNo
            have hF1 := insert_answerReadsKept c Z _ _
              (.schedContext (donationReturnSchedContext sc owner (head?.bind fun p => p.snd.prev)))
              (objects_of_getSchedContext? hS) hNo (fun _ => rfl)
            dsimp only at h
            cases hP : storeDonationHeadPop scId head? _ with
            | error e => rw [hP] at h; cases h
            | ok Zb =>
              rw [hP] at h
              have hNo2 := storeDonationHeadPop_noResizeDue _ _ scId head? hNo1 hP
              have hF2 := hF1.trans (storeDonationHeadPop_answerReadsKept c _ _ scId head? hNo1 hP)
              dsimp only at h
              cases hL : lookupTcb Zb owner with
              | none => rw [hL] at h; cases h
              | some ct =>
                rw [hL] at h
                dsimp only at h
                cases hC : storeObject owner.toObjId _ Zb with
                | error e => rw [hC] at h; cases h
                | ok p =>
                  obtain ⟨⟨⟩, Zc⟩ := p
                  rw [hC] at h
                  have hNo3 := tcbStore_noResizeDue _ _ _ _ _ hL hNo2 hC
                  have hF3 := hF2.trans (tcbStore_answerReadsKept c _ _ _ _ _ hL hNo2 (by rfl) hC)
                  dsimp only at h
                  cases hL3 : lookupTcb Zc server with
                  | none => rw [hL3] at h; cases h
                  | some st' =>
                    rw [hL3] at h
                    dsimp only at h
                    cases hC3 : storeObject server.toObjId _ Zc with
                    | error e => rw [hC3] at h; cases h
                    | ok p =>
                      obtain ⟨⟨⟩, Zd⟩ := p
                      rw [hC3] at h
                      cases h
                      refine hF3.trans ((tcbStore_answerReadsKept c _ _ _ _ _ hL3 hNo3 (by rfl) hC3).trans ?_)
                      apply answerReadsKept_of_objects
                      rw [markKeyChangeFrom_objects, markKeyChangeFrom_objects]

theorem answerReadsKept_of_getTcb? {c : SeLe4n.ThreadId} {X Y : SystemState}
    (h : Y.getTcb? c = X.getTcb? c) : answerReadsKept c X Y := by
  unfold answerReadsKept; rw [h]

theorem migrateSchedContextReplenishment_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState)
    (scId : SeLe4n.SchedContextId) (a b : CoreId) :
    answerReadsKept c Z (migrateSchedContextReplenishment Z scId a b) :=
  answerReadsKept_of_getTcb? ((migrateSchedContextReplenishment_agree Z scId a b).getTcb? c)

theorem popHeldReplyHead_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue)
    (h : popHeldReplyHead Z holder scId owner = .ok Z') : answerReadsKept c Z Z' := by
  unfold popHeldReplyHead returnDonatedSchedContextResolved keepDonatedSchedContextResolved at h
  split at h
  · cases hN : replyStackOuterCaller? Z scId with
    | error e => rw [hN] at h; cases h
    | ok n => rw [hN] at h; exact returnDonatedSchedContext_answerReadsKept c Z Z' holder scId owner n hNo h
  · cases hN : replyStackOuterCaller? Z scId with
    | error e => rw [hN] at h; cases h
    | ok n => rw [hN] at h; exact keepDonatedSchedContext_answerReadsKept c Z Z' holder scId n hNo h

theorem cleanupPreReceiveDonationChecked_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (x : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) (h : cleanupPreReceiveDonationChecked Z x = .ok Z') :
    answerReadsKept c Z Z' := by
  unfold cleanupPreReceiveDonationChecked at h
  cases hL : lookupTcb Z x with
  | none => rw [hL] at h; cases h; exact .refl _
  | some t =>
    rw [hL] at h
    dsimp only at h
    split at h
    · exact popHeldReplyHead_answerReadsKept c Z Z' x _ _ hNo h
    all_goals (cases h; exact .refl _)

theorem cleanupPreReceiveDonationMigrated_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (x : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) (h : cleanupPreReceiveDonationMigrated Z x = .ok Z') :
    answerReadsKept c Z Z' := by
  obtain ⟨Zc, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  refine (cleanupPreReceiveDonationChecked_answerReadsKept c Z Zc x hNo hC).trans ?_
  unfold preReceiveReturnMigration
  split
  · exact migrateSchedContextReplenishment_answerReadsKept c _ _ _ _
  · exact .refl _

theorem recordReplyStasher_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState) (code : Nat)
    (t : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    answerReadsKept c Z (Z.recordReplyStasher code t) := by
  unfold SystemState.recordReplyStasher
  rcases code with _ | k
  · exact .refl _
  · dsimp only
    cases hR : Z.getReply? ⟨k⟩ with
    | none => exact .refl _
    | some x =>
      dsimp only
      rw [storeObject_eq_of_leaves (storeLeaves_reply hR _)]
      exact insert_answerReadsKept c Z _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hNo
        (by intro; rfl)

theorem endpointQueueEnqueue_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState) (k : SeLe4n.ObjId)
    (isRecv : Bool) (t : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue)
    (h : endpointQueueEnqueue k isRecv t Z = .ok Z') : answerReadsKept c Z Z' := by
  unfold endpointQueueEnqueue at h
  cases hO : Z.getObject? k with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o with
    | endpoint ep =>
      have hk : Z.objects[k]? = some (.endpoint ep) := hO
      have hL : ∀ e : Endpoint, storeLeavesIndexAndTypes Z k (KernelObject.endpoint e).objectType = true :=
        fun e => by unfold storeLeavesIndexAndTypes storeKeepsKind; rw [hk]; rfl
      have hNoE : ∀ e : Endpoint,
          ({ Z with objects := Z.objects.insert k (.endpoint e) } : SystemState).objects.noResizeDue :=
        fun e => insert_present_noResizeDue Z k _ _ hk hNo
      have hE : ∀ e : Endpoint, answerReadsKept c Z { Z with objects := Z.objects.insert k (.endpoint e) } :=
        fun e => insert_answerReadsKept c Z k _ (.endpoint e) hk hNo (fun _ => rfl)
      dsimp only at h
      cases hLt : lookupTcb Z t with
      | none => rw [hLt] at h; cases h
      | some tcb =>
        rw [hLt] at h
        dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · rw [storeObject_eq_of_leaves (hL _)] at h
              exact (hE _).trans (storeTcbQueueLinks_answerReadsKept c _ _ _ _ _ _ (hNoE _) h)
            · split at h
              · cases h
              · rw [storeObject_eq_of_leaves (hL _)] at h
                dsimp only at h
                split at h
                · cases h
                · rename_i Zb hS
                  exact ((hE _).trans (storeTcbQueueLinks_answerReadsKept c _ _ _ _ _ _ (hNoE _) hS)).trans
                    (storeTcbQueueLinks_answerReadsKept c _ _ _ _ _ _
                      (storeTcbQueueLinks_noResizeDue' _ _ _ _ _ _ (hNoE _) hS) h)
    | _ => cases h

theorem endpointReceiveDualOnCore_answerReadsKept_of_sender (c : SeLe4n.ThreadId) (Z : SystemState)
    (k : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId) (ec : CoreId) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (hE : Z.getEndpoint? k = some ep) (hS : ep.sendQ.head = some s)
    (hs : s ≠ c) (ht : tid ≠ c) (hNo : Z.objects.noResizeDue) :
    answerReadsKept c Z (endpointReceiveDualOnCore k tid rid ec Z).1 := by
  have hk : Z.objects[k]? = some (.endpoint ep) := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE
  unfold endpointReceiveDualOnCore
  rw [hE]
  dsimp only
  rw [hS]
  dsimp only
  cases hP : endpointQueuePopHead k false Z with
  | error e => exact .refl _
  | ok p =>
    obtain ⟨sender, stcb, Za⟩ := p
    have hsend : sender = s := endpointQueuePopHead_popped_eq_head k false Z Za ep sender s stcb hk
      (by simp [hS]) hP
    subst hsend
    have hNo1 := endpointQueuePopHead_noResizeDue Z k false sender stcb Za hNo hP
    have hF1 := endpointQueuePopHead_answerReadsKept c Z k false sender stcb Za hNo hP
    dsimp only
    split
    · simp only [↓reduceIte]
      split
      · cases h2 : storeTcbIpcStateAndMessage Za sender (.blockedOnReply k (some tid)) none with
        | error e => exact .refl _
        | ok Zb =>
          have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
          have hF2 := hF1.trans (storeTcbIpcStateAndMessage_answerReadsKept c Za Zb _ _ _ hNo1 hs h2)
          cases rid with
          | none => exact .refl _
          | some rid =>
            dsimp only
            cases h3 : SystemState.linkCallerReply sender rid Zb with
            | error e => exact .refl _
            | ok p3 =>
              obtain ⟨⟨⟩, Zc⟩ := p3
              have hNo3 := linkCallerReply_noResizeDue Zb Zc sender rid hNo2 h3
              have hF3 := hF2.trans (linkCallerReply_answerReadsKept c Zb Zc sender rid hNo2 hs h3)
              dsimp only
              cases h4 : storeTcbIpcStateAndMessage Zc tid .ready _ with
              | error e => exact .refl _
              | ok Zd =>
                exact (hF3.trans (storeTcbIpcStateAndMessage_answerReadsKept c Zc Zd _ _ _ hNo3 ht h4)).trans
                  (linkReplyWaiter_answerReadsKept c Zd sender tid)
      · cases h2 : storeTcbIpcStateAndMessage Za sender .ready none with
        | error e => exact .refl _
        | ok Zb =>
          have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
          have hF2 := hF1.trans (storeTcbIpcStateAndMessage_answerReadsKept c Za Zb _ _ _ hNo1 hs h2)
          dsimp only
          cases h4 : storeTcbIpcStateAndMessage (Zb.updateTcb sender fun t => { t with threadState := .Inactive })
              tid .ready _ with
          | error e => exact .refl _
          | ok Zd =>
            exact (hF2.trans (updateTcb_answerReadsKept c sender Zb _ hNo2 (fun e => absurd e hs))).trans
              (storeTcbIpcStateAndMessage_answerReadsKept c _ Zd _ _ _ (updateTcb_noResizeDue _ _ _ hNo2) ht h4)
    · simp only [↓reduceIte, Bool.false_eq_true]
      cases h2 : storeTcbIpcStateAndMessage Za sender .ready none with
      | error e => exact .refl _
      | ok Zb =>
        have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
        have hF2 := hF1.trans (storeTcbIpcStateAndMessage_answerReadsKept c Za Zb _ _ _ hNo1 hs h2)
        dsimp only
        cases h4 : storeTcbIpcStateAndMessage (wakeThread Zb sender ec).1 tid .ready _ with
        | error e => exact .refl _
        | ok Zd =>
          exact (hF2.trans (wakeThread_answerReadsKept c Zb sender ec hNo2 hs)).trans
            (storeTcbIpcStateAndMessage_answerReadsKept c _ Zd _ _ _ (wakeThread_noResizeDue _ _ _ hNo2) ht h4)

/-- **The receive body keeps what the stage reads off a thread that is neither
the receiver nor its send queue's head.** -/
theorem endpointReceiveDualOnCore_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState) (k : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId) (ec : CoreId)
    (hHead : receiveRendezvousSender? Z k ≠ some c) (ht : tid ≠ c) (hNo : Z.objects.noResizeDue) :
    answerReadsKept c Z (endpointReceiveDualOnCore k tid rid ec Z).1 := by
  cases hE : Z.getEndpoint? k with
  | none =>
    unfold endpointReceiveDualOnCore
    rw [hE]
    dsimp only
    split <;> exact .refl _
  | some ep =>
    cases hS : ep.sendQ.head with
    | some s =>
      have hs : s ≠ c := fun e => hHead (by unfold receiveRendezvousSender?; rw [hE]; simp [hS, e])
      exact endpointReceiveDualOnCore_answerReadsKept_of_sender c Z k tid rid ec ep s hE hS hs ht hNo
    | none =>
      unfold endpointReceiveDualOnCore
      rw [hE]
      dsimp only
      rw [hS]
      dsimp only
      cases hC : cleanupPreReceiveDonationMigrated Z tid with
      | error e => exact .refl _
      | ok Zc =>
        have hNoC := cleanupPreReceiveDonationMigrated_noResizeDue Z Zc tid hNo hC
        have hFC := cleanupPreReceiveDonationMigrated_answerReadsKept c Z Zc tid hNo hC
        dsimp only
        cases hQ : endpointQueueEnqueue k true tid Zc with
        | error e => exact .refl _
        | ok Zq =>
          have hNoQ := endpointQueueEnqueue_noResizeDue Zc Zq k true tid hNoC hQ
          have hFQ := hFC.trans (endpointQueueEnqueue_answerReadsKept c Zc Zq k true tid hNoC hQ)
          dsimp only
          cases hB : storeTcbIpcStateAndMessage Zq tid (.blockedOnReceive k) none with
          | error e => exact .refl _
          | ok Zb =>
            have hNoB := storeTcbIpcStateAndMessage_noResizeDue Zq Zb _ _ _ hNoQ hB
            have hFB := hFQ.trans (storeTcbIpcStateAndMessage_answerReadsKept c Zq Zb _ _ _ hNoQ ht hB)
            dsimp only
            cases hT : Zb.getTcb? tid with
            | none =>
              exact hFB.trans (removeRunnableOnCore_answerReadsKept c Zb tid ec)
            | some rTcb =>
              dsimp only
              split
              · have hNoS := recordReplyStasher_noResizeDue Zb (SeLe4n.ReplyId.optCode rid) tid hNoB
                have hFS := hFB.trans (recordReplyStasher_answerReadsKept c Zb (SeLe4n.ReplyId.optCode rid) tid hNoB)
                have hT' : (Zb.recordReplyStasher (SeLe4n.ReplyId.optCode rid) tid).getTcb? tid = some rTcb := by
                  rw [recordReplyStasher_getTcb?_of_noResizeDue _ _ _ _ hNoB, hT]
                cases hO : storeObject tid.toObjId (.tcb { rTcb with
                    pendingReceiveReplyCode := SeLe4n.ReplyId.optCode rid })
                    (Zb.recordReplyStasher (SeLe4n.ReplyId.optCode rid) tid) with
                | error e => exact .refl _
                | ok p =>
                  obtain ⟨⟨⟩, Zs⟩ := p
                  exact (hFS.trans (storeObject_answerReadsKept c _ Zs _ _ _
                    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT') hNoS
                    (fun e => absurd e (ne_toObjId ht)) hO)).trans
                    (removeRunnableOnCore_answerReadsKept c Zs tid ec)
              · exact .refl _

/-- A state after `Z` with no resize due that keeps what the stage reads off `c`. -/
def KeepsAnswerReads (c : SeLe4n.ThreadId) (Z s : SystemState) : Prop :=
  s.objects.noResizeDue ∧ answerReadsKept c Z s

namespace KeepsAnswerReads
variable {c : SeLe4n.ThreadId} {Z s : SystemState}

theorem mapValueAt (h : KeepsAnswerReads c Z s) (k : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hF : ∀ o, s.objects[k]? = some o → answerReadsOf (some (F o)) = answerReadsOf (some o)) :
    KeepsAnswerReads c Z { s with objects := s.objects.mapValueAt k F } := by
  refine ⟨(RHTable.noResizeDue_mapValueAt _ _ _).mpr h.1, ?_⟩
  refine (h.2.trans (answerReadsKept_of_objects ?_))
  show answerReadsOf ((s.objects.mapValueAt k F)[c.toObjId]?) = _
  simp only [RHTable_getElem?_eq_get?, RHTable.get?_mapValueAt]
  split
  · next hk =>
    have hk' : k = c.toObjId := beq_iff_eq.mp hk
    subst hk'
    cases hg : s.objects.get? c.toObjId with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      exact hF o (by simpa only [RHTable_getElem?_eq_get?] using hg)
  · rfl

theorem setSlotLinkWords (h : KeepsAnswerReads c Z s) (o : SeLe4n.ObjId) (sl : SeLe4n.Slot) (f : LinkField)
    (x w : Nat) : KeepsAnswerReads c Z (s.setSlotLinkWords o sl f x w) := by
  rw [setSlotLinkWords_eq_modifyObject _ _ _ _ _ _ h.1, SystemState.modifyObject_eq_mapValueAt _ _ _ h.1]
  exact h.mapValueAt o _ (fun o' _ => by cases o' <;> rfl)

theorem linkAddChild (h : KeepsAnswerReads c Z s) (p q : SlotRef) :
    KeepsAnswerReads c Z (s.linkAddChild p q) := by
  unfold SystemState.linkAddChild
  dsimp only
  split <;> (repeat apply KeepsAnswerReads.setSlotLinkWords) <;> exact h

theorem cdtAddChild (h : KeepsAnswerReads c Z s) (p q : SlotRef) (op : DerivationOp) :
    KeepsAnswerReads c Z (s.cdtAddChild p q op) :=
  KeepsAnswerReads.linkAddChild (s := s.modifyCdt _) h p q

theorem storeObject_cnode {s' : SystemState} (h : KeepsAnswerReads c Z s) (k : SeLe4n.ObjId) (cn0 cn : CNode)
    (hk : s.objects[k]? = some (.cnode cn0)) (hS : storeObject k (.cnode cn) s = .ok ((), s')) :
    KeepsAnswerReads c Z s' :=
  ⟨storeObject_present_noResizeDue s s' k _ (.cnode cn) hk h.1
    (by unfold storeLeavesIndexAndTypes storeKeepsKind; rw [hk]; rfl) hS,
   h.2.trans (storeObject_answerReadsKept c s s' k _ _ hk h.1 (by intro; rfl) hS)⟩

theorem storeCNodeWith (h : KeepsAnswerReads c Z s) (k : SeLe4n.ObjId) (f : CNode → CNode) :
    KeepsAnswerReads c Z (s.storeCNodeWith k f) := by
  rcases SystemState.storeCNodeWith_cases s k f with ⟨cn, hk, hS⟩ | e
  · exact h.storeObject_cnode k cn (f cn) hk hS
  · rw [e]; exact h

theorem untypedSourceSetFull (h : KeepsAnswerReads c Z s) (src : CSpaceAddr) (cap : Capability) :
    KeepsAnswerReads c Z (SeLe4n.Kernel.untypedSourceSetFull s src cap) :=
  untypedSourceSetFull_of (P := KeepsAnswerReads c Z) h (fun _ => h.storeCNodeWith _ _)

theorem ipcTransferSingleCap {s' : SystemState} (h : KeepsAnswerReads c Z s)
    (cap : Capability) (src : SlotRef) (dst : CSpaceAddr)
    (hT : SeLe4n.Kernel.ipcTransferSingleCap cap src dst s = .ok ((), s')) : KeepsAnswerReads c Z s' := by
  obtain ⟨_, s2, -, -, -, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases hT
  obtain ⟨cn, hC, -, -, hS⟩ := cspaceInsertSlot_ok_decompose _ _ _ _ hIns
  exact ((h.storeObject_cnode _ cn _ ((SystemState.getCNode?_eq_some_iff _ _ _).mp hC)
    hS).cdtAddChild _ _ _).untypedSourceSetFull _ _

theorem recordUnwrappedBadge (h : KeepsAnswerReads c Z s) (rtcb : TCB) (i : Nat) (b : SeLe4n.Badge) :
    KeepsAnswerReads c Z (SeLe4n.Kernel.recordUnwrappedBadge s rtcb i b) := by
  have hO := recordUnwrappedBadge_objects s rtcb i b
  exact ⟨hO ▸ h.1, h.2.trans (answerReadsKept_of_objects (by rw [hO]))⟩

end KeepsAnswerReads

/-- **The capability transfer keeps what the stage reads off every thread.** -/
theorem receiveTransferCaps_answerReadsKept (c : SeLe4n.ThreadId)
    (req : Option (Capability × Array SeLe4n.CPtr))
    (endpointId : Option SeLe4n.ObjId) (target? : Option (TCB × Option CSpaceAddr))
    {Z Z' : SystemState} {r : CapTransferSummary} (hNo : Z.objects.noResizeDue)
    (h : receiveTransferCaps req endpointId target? Z = .ok (r, Z')) : KeepsAnswerReads c Z Z' := by
  have hK : KeepsAnswerReads c Z Z := ⟨hNo, .refl _⟩
  unfold receiveTransferCaps at h
  rcases req with _ | ⟨root, addrs⟩
  · cases h; exact hK
  · simp only [] at h
    split at h
    · cases h; exact hK
    · rcases target? with _ | ⟨rtcb, slot?⟩
      · cases h; exact hK
      · exact ipcUnwrapCapsLoop_rel (fun a b => KeepsAnswerReads c Z b → KeepsAnswerReads c Z a)
          (fun _ h => h) (fun _ _ _ h1 h2 h => h1 (h2 h)) _ _ rtcb
          (fun s i b h => h.recordUnwrappedBadge rtcb i b) _ _ _ _ _ _ _
          (fun _ _ _ _ _ _ hT h => h.ipcTransferSingleCap _ _ _ hT) h hK

/-- **The capability-carrying receive keeps what the stage reads off a thread
that is neither the receiver nor its send queue's head.** -/
theorem endpointReceiveDualWithCapsOnCore_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState)
    (k : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId) (ec : CoreId)
    (hHead : receiveRendezvousSender? Z k ≠ some c) (ht : tid ≠ c) (hNo : Z.objects.noResizeDue) :
    answerReadsKept c Z (endpointReceiveDualWithCapsOnCore k tid rid ec Z).1 := by
  have hF := endpointReceiveDualOnCore_answerReadsKept c Z k tid rid ec hHead ht hNo
  have hNo1 := endpointReceiveDualOnCore_noResizeDue Z k tid rid ec hNo
  unfold endpointReceiveDualWithCapsOnCore
  dsimp only
  cases hR : endpointReceiveDualOnCore k tid rid ec Z with
  | mk Za res =>
    rw [hR] at hF hNo1
    cases res with
    | error e => exact hF
    | ok p =>
      obtain ⟨sid, sgi⟩ := p
      dsimp only
      split
      · exact hF
      · cases hT : receiveTransferCaps (receiveCapRequest Z k) (some k) (receiverCapTarget? Z tid) Za with
        | error e => exact hF
        | ok q =>
          obtain ⟨sm, Zb⟩ := q
          exact hF.trans (receiveTransferCaps_answerReadsKept c _ _ _ hNo1 hT).2

theorem answerReadsKept_of_releaseAgree {c : SeLe4n.ThreadId} {X Y : SystemState}
    (h : Y.objectsAgreeOffReleaseLinks X) : answerReadsKept c X Y :=
  answerReadsKept_of_getTcb? (h.getTcb? c)

theorem updateSchedContext_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState)
    (scId : SeLe4n.SchedContextId) (f : SchedContext → SchedContext) (hNo : Z.objects.noResizeDue) :
    KeepsAnswerReads c Z (Z.updateSchedContext scId f) := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  split
  · rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
    exact KeepsAnswerReads.mapValueAt ⟨hNo, .refl _⟩ _ _ (fun o _ => by cases o <;> rfl)
  · exact ⟨hNo, .refl _⟩

theorem schedContextReturnLinks_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState)
    (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    answerReadsKept c Z (schedContextReturnLinks Z vS tid) := by
  rw [schedContextReturnLinks_eq_impl]
  unfold schedContextReturnLinksImpl
  cases Z.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => exact .refl _
  | some _ =>
    cases Z.getTcb? tid with
    | none => exact .refl _
    | some tcb =>
      dsimp only
      have h1 := updateSchedContext_answerReadsKept c Z (SeLe4n.SchedContextId.ofObjId vS.val)
        (fun sc => { sc with boundThreadCode := 0 }) hNo
      have h2 := h1.2.trans (updateTcb_answerReadsKept c tid _
        (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) h1.1 (fun _ _ => rfl))
      refine h2.trans (answerReadsKept_of_objects ?_)
      rw [markKeyChangeParts_objects, markCandidacyGainFor_objects]
      split <;> rfl

theorem schedContextReturnPerform_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState)
    (vS : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    answerReadsKept c Z (schedContextReturnPerform Z vS tid) := by
  unfold schedContextReturnPerform SchedContextOps.purgeReplenishment
  exact (schedContextReturnLinks_answerReadsKept c Z vS tid hNo).trans
    (answerReadsKept_of_releaseAgree (SystemState.releaseRemoveAnywhere_agree _ _))

/-- **The receive's context return keeps what the stage reads off every thread.** -/
theorem receiveReturnSchedContext_answerReadsKept (c : SeLe4n.ThreadId) (blocks : Bool) (Z : SystemState)
    (tid : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    answerReadsKept c Z (receiveReturnSchedContext blocks Z tid) := by
  unfold receiveReturnSchedContext
  cases blocks with
  | false => exact .refl _
  | true =>
    simp only [↓reduceIte]
    cases Z.getTcb? tid with
    | none => exact .refl _
    | some t =>
      dsimp only
      split
      · exact .refl _
      unfold maybeReturnSchedContext
      cases Z.getNotification? _ with
      | none => exact .refl _
      | some ntfn =>
        dsimp only
        cases ntfn.schedContext with
        | none => exact .refl _
        | some s =>
          dsimp only
          split
          · split
            · exact schedContextReturnPerform_answerReadsKept c Z _ tid hNo
            · exact .refl _
          · exact .refl _


section PostReceive

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

theorem donationPushFrame?_answer (Z : SystemState) (t : TCB) :
    donationPushFrame? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t = donationPushFrame? Z t := by
  unfold donationPushFrame?
  cases t.replyObject with
  | none => rfl
  | some rid => dsimp only; rw [getReply?_answer]

theorem donationPushRefusal?_answer (Z : SystemState) (server : SeLe4n.ThreadId)
    (old? : Option SeLe4n.ReplyId) (pushRid : SeLe4n.ReplyId) :
    donationPushRefusal? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) server old? pushRid =
      donationPushRefusal? Z server old? pushRid := by
  unfold donationPushRefusal?
  have hT : (lookupTcb (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) server).isNone =
      (lookupTcb Z server).isNone := by
    rw [lookupTcb_answer']; cases lookupTcb Z server <;> rfl
  simp only [getReply?_answer, hT]

theorem storeDonationFramePush_answer (Z : SystemState) (scId : SeLe4n.SchedContextId)
    (pushRid : SeLe4n.ReplyId) (pushReply : Reply) (old? : Option SeLe4n.ReplyId)
    (hP : Z.getReply? pushRid ≠ none) (hNo : Z.objects.noResizeDue) :
    storeDonationFramePush scId pushRid pushReply old? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      (storeDonationFramePush scId pushRid pushReply old? Z).map
        (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold storeDonationFramePush
  split
  · rfl
  · cases hR : Z.getReply? pushRid with
    | none => exact absurd hR hP
    | some x =>
      have hk := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
      rw [storeObject_answer r ρ μ κ Z _ _ _ hk hNo (storeLeaves_reply hR _) (.inr ⟨rfl, rfl⟩),
        storeObject_eq_of_leaves (storeLeaves_reply hR _)]
      have hNo1 := insert_present_noResizeDue Z _ _
        (.reply { pushReply with prev := old?, next := some (.head scId) }) hk hNo
      dsimp only [mapStepState]
      cases old? with
      | none => rfl
      | some old =>
        dsimp only
        rw [getReply?_answer]
        split
        · rfl
        · rename_i oldR hO
          rw [storeObject_answer r ρ μ κ _ _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hO) hNo1
              (storeLeaves_reply hO _) (.inr ⟨rfl, rfl⟩)]
          cases storeObject old.toObjId (.reply { oldR with next := some (.frame pushRid) }) _ with
          | error e => rfl
          | ok p => obtain ⟨⟨⟩, Zb⟩ := p; rfl

theorem getReply?_after_schedContext_store (Z : SystemState) (scId : SeLe4n.SchedContextId) (sc0 sc : SchedContext)
    (hS : Z.getSchedContext? scId = some sc0) (hNo : Z.objects.noResizeDue) (rid : SeLe4n.ReplyId) :
    SystemState.getReply? { Z with objects := Z.objects.insert scId.toObjId (.schedContext sc) } rid =
      Z.getReply? rid := by
  have hk := objects_of_getSchedContext? hS
  have e := objects_insert_present Z _ _ (.schedContext sc) hk hNo rid.toObjId
  unfold SystemState.getReply?
  by_cases hq : scId.toObjId = rid.toObjId
  · rw [if_pos (beq_iff_eq.mpr hq)] at e
    have e2 : Z.objects[rid.toObjId]? = some (.schedContext sc0) := hq ▸ hk
    simp only [e, e2]
  · rw [if_neg (fun h => hq (beq_iff_eq.mp h))] at e
    simp only [e]

theorem storeDonationFramePush_noResizeDue (Z Z' : SystemState) (scId : SeLe4n.SchedContextId)
    (pushRid : SeLe4n.ReplyId) (pushReply : Reply) (old? : Option SeLe4n.ReplyId)
    (hP : Z.getReply? pushRid ≠ none) (hNo : Z.objects.noResizeDue)
    (h : storeDonationFramePush scId pushRid pushReply old? Z = .ok Z') : Z'.objects.noResizeDue := by
  unfold storeDonationFramePush at h
  split at h
  · cases h
  · cases hR : Z.getReply? pushRid with
    | none => exact absurd hR hP
    | some x =>
      have hk := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
      rw [storeObject_eq_of_leaves (storeLeaves_reply hR _)] at h
      have hNo1 := fun o => insert_present_noResizeDue Z pushRid.toObjId _ o hk hNo
      dsimp only at h
      cases old? with
      | none => cases h; exact hNo1 _
      | some old =>
        dsimp only at h
        split at h
        · cases h
        · rename_i oldR hO
          cases hS : storeObject old.toObjId (.reply { oldR with next := some (.frame pushRid) }) _ with
          | error e => rw [hS] at h; cases h
          | ok p =>
            obtain ⟨⟨⟩, Zb⟩ := p
            rw [hS] at h; cases h
            exact storeObject_present_noResizeDue _ _ _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hO)
              (hNo1 _) (storeLeaves_reply hO _) hS

theorem donateSchedContext_answer (Z : SystemState) (client server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : Z.objects.noResizeDue) :
    donateSchedContext (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) client server scId =
      (donateSchedContext Z client server scId).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold donateSchedContext
  rw [getSchedContext?_answer]
  cases hS : Z.getSchedContext? scId with
  | none => rfl
  | some sc =>
    dsimp only
    split
    · rfl
    · rw [lookupTcb_answer']
      cases hL : lookupTcb Z client with
      | none => rfl
      | some ct =>
        dsimp only [Option.map]
        rw [donationPushFrame?_answer]
        have hD : donationPushFrame? Z (if r = client then TCB.withAnswerSlots ρ μ id κ ct else ct) =
            donationPushFrame? Z ct := by split <;> rfl
        rw [hD]
        cases hP : donationPushFrame? Z ct with
        | error e => rfl
        | ok q =>
          obtain ⟨pushRid, pushReply⟩ := q
          obtain ⟨-, hR, -⟩ := donationPushFrame?_ok Z ct pushRid pushReply hP
          dsimp only
          rw [donationPushRefusal?_answer]
          cases donationPushRefusal? Z server sc.scReply pushRid
          case some => rfl
          dsimp only
          rw [storeObject_answer r ρ μ κ Z _ _ _ (objects_of_getSchedContext? hS) hNo
              (storeLeaves_schedContext hS _) (.inr ⟨rfl, rfl⟩),
            storeObject_eq_of_leaves (storeLeaves_schedContext hS _)]
          have hNo1 := fun o => insert_present_noResizeDue Z _ _ o (objects_of_getSchedContext? hS) hNo
          dsimp only [mapStepState]
          rw [storeDonationFramePush_answer r ρ μ κ _ scId pushRid pushReply sc.scReply
            (by rw [getReply?_after_schedContext_store Z scId sc _ hS hNo, hR]; simp) (hNo1 _)]
          cases hF : storeDonationFramePush scId pushRid pushReply sc.scReply _ with
          | error e => rfl
          | ok Zb =>
            have hNo2 := storeDonationFramePush_noResizeDue _ _ scId pushRid pushReply sc.scReply
              (by rw [getReply?_after_schedContext_store Z scId sc _ hS hNo, hR]; simp) (hNo1 _) hF
            dsimp only [Except.map]
            rw [lookupTcb_answer']
            cases hL2 : lookupTcb Zb client with
            | none => rfl
            | some ct2 =>
              dsimp only [Option.map]
              have h1 := storeObject_tcb_answer r ρ μ κ Zb client ct2
                (fun y => { y with scBindingScCode := 0, scBindingOwnerCode := 0 })
                (getTcb?_of_lookupTcb _ _ _ hL2) hNo2 (fun _ _ => rfl)
              simp only [] at h1
              rw [h1]
              cases hC : storeObject client.toObjId _ Zb with
              | error e => rfl
              | ok p =>
                obtain ⟨⟨⟩, Zc⟩ := p
                have hNo3 := storeObject_present_noResizeDue Zb Zc _ _ (.tcb _)
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp (getTcb?_of_lookupTcb _ _ _ hL2)) hNo2
                  (storeLeavesIndexAndTypes_tcb_of_getTcb? (getTcb?_of_lookupTcb _ _ _ hL2)) hC
                dsimp only [mapStepState]
                rw [lookupTcb_answer']
                cases hL3 : lookupTcb Zc server with
                | none => rfl
                | some st3 =>
                  dsimp only [Option.map]
                  have h2 := storeObject_tcb_answer r ρ μ κ Zc server st3
                    (fun y => { y with
                      scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.donated scId client),
                      scBindingOwnerCode := SeLe4n.Kernel.SchedContextBinding.ownerCode (.donated scId client) })
                    (getTcb?_of_lookupTcb _ _ _ hL3) hNo3 (fun _ _ => rfl)
                  simp only [] at h2
                  rw [h2]
                  cases storeObject server.toObjId _ Zc with
                  | error e => rfl
                  | ok p =>
                    obtain ⟨⟨⟩, Zd⟩ := p
                    dsimp only [mapStepState, Except.map]
                    rw [markKeyChangeFrom_answer, markKeyChangeFrom_answer]

theorem callDonationSchedContext?_answer (Z : SystemState) (caller receiver : SeLe4n.ThreadId) :
    callDonationSchedContext? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) caller receiver =
      callDonationSchedContext? Z caller receiver := by
  unfold callDonationSchedContext?
  rw [lookupTcb_answer']
  cases lookupTcb Z receiver with
  | none => rfl
  | some rt =>
    dsimp only [Option.map]
    have hB : (if r = receiver then TCB.withAnswerSlots ρ μ id κ rt else rt).schedContextBinding =
        rt.schedContextBinding := by split <;> rfl
    rw [hB]
    cases rt.schedContextBinding with
    | unbound =>
      dsimp only
      rw [lookupTcb_answer']
      cases lookupTcb Z caller with
      | none => rfl
      | some ct => dsimp only [Option.map]; split <;> rfl
    | _ => rfl

theorem applyCallDonation_answer (Z : SystemState) (cV rV : SeLe4n.ValidThreadId)
    (hNo : Z.objects.noResizeDue) :
    applyCallDonation (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) cV rV =
      (applyCallDonation Z cV rV).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold applyCallDonation
  dsimp only
  rw [lookupTcb_answer']
  cases lookupTcb Z rV.val with
  | none => rfl
  | some rt =>
    dsimp only [Option.map]
    have hB : (if r = rV.val then TCB.withAnswerSlots ρ μ id κ rt else rt).schedContextBinding =
        rt.schedContextBinding := by split <;> rfl
    rw [hB]
    cases rt.schedContextBinding with
    | unbound =>
      dsimp only
      rw [lookupTcb_answer']
      cases lookupTcb Z cV.val with
      | none => rfl
      | some ct =>
        dsimp only [Option.map]
        have hC : (if r = cV.val then TCB.withAnswerSlots ρ μ id κ ct else ct).schedContextBinding =
            ct.schedContextBinding := by split <;> rfl
        rw [hC]
        cases ct.schedContextBinding.scId? with
        | none => rfl
        | some scId =>
          dsimp only
          rw [donateSchedContextValid_eq, donateSchedContextValid_eq,
            donateSchedContext_answer r ρ μ κ Z _ _ scId hNo]
          cases donateSchedContext Z cV.val rV.val scId <;> rfl
    | _ => rfl

theorem applyRendezvousCallDonation_answer (Z : SystemState) (receiver donor : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) :
    applyRendezvousCallDonation (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) receiver donor =
      (applyRendezvousCallDonation Z receiver donor).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold applyRendezvousCallDonation
  split
  · rename_i dV rV _ _
    unfold applyCallDonationOnCore
    rw [applyCallDonation_answer r ρ μ κ Z dV rV hNo, callDonationSchedContext?_answer,
      determineTargetCore_answer, determineTargetCore_answer]
    cases applyCallDonation Z dV rV with
    | error e => rfl
    | ok Za =>
      dsimp only [Except.map]
      cases callDonationSchedContext? Z dV.val rV.val with
      | none => rfl
      | some scId => dsimp only; rw [migrateSchedContextReplenishment_mapTcbInPlace]
  · rfl


theorem descheduleAtPlacement_noResizeDue (Z : SystemState) (t : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) : (descheduleAtPlacement Z t).objects.noResizeDue := by
  unfold descheduleAtPlacement descheduleAt
  cases placedCoreOf? Z t with
  | none => exact hNo
  | some k => exact removeRunnableOnCore_noResizeDue Z t k hNo

theorem replyRecvHolderDeschedule_noResizeDue (tid holder : SeLe4n.ThreadId) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) : (replyRecvHolderDeschedule tid holder Z).objects.noResizeDue := by
  unfold replyRecvHolderDeschedule
  split
  · exact hNo
  · exact descheduleAtPlacement_noResizeDue Z holder hNo

theorem donateSchedContext_noResizeDue (Z Z' : SystemState) (client server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : Z.objects.noResizeDue)
    (h : donateSchedContext Z client server scId = .ok Z') : Z'.objects.noResizeDue := by
  unfold donateSchedContext at h
  cases hS : Z.getSchedContext? scId with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h
    dsimp only at h
    split at h
    · cases h
    · cases hL : lookupTcb Z client with
      | none => rw [hL] at h; cases h
      | some ct =>
        rw [hL] at h
        dsimp only at h
        cases hP : donationPushFrame? Z ct with
        | error e => rw [hP] at h; cases h
        | ok q =>
          obtain ⟨pushRid, pushReply⟩ := q
          obtain ⟨-, hR, -⟩ := donationPushFrame?_ok Z ct pushRid pushReply hP
          rw [hP] at h
          dsimp only at h
          cases hAd : donationPushRefusal? Z server sc.scReply pushRid
          case some => rw [hAd] at h; cases h
          rw [hAd] at h
          dsimp only at h
          rw [storeObject_eq_of_leaves (storeLeaves_schedContext hS _)] at h
          have hNo1 := fun o => insert_present_noResizeDue Z _ _ o (objects_of_getSchedContext? hS) hNo
          dsimp only at h
          cases hF : storeDonationFramePush scId pushRid pushReply sc.scReply _ with
          | error e => rw [hF] at h; cases h
          | ok Zb =>
            rw [hF] at h
            have hNo2 := storeDonationFramePush_noResizeDue _ _ scId pushRid pushReply sc.scReply
              (by rw [getReply?_after_schedContext_store Z scId sc _ hS hNo, hR]; simp) (hNo1 _) hF
            dsimp only at h
            cases hL2 : lookupTcb Zb client with
            | none => rw [hL2] at h; cases h
            | some ct2 =>
              rw [hL2] at h
              dsimp only at h
              cases hC : storeObject client.toObjId _ Zb with
              | error e => rw [hC] at h; cases h
              | ok p =>
                obtain ⟨⟨⟩, Zc⟩ := p
                rw [hC] at h
                have hNo3 := tcbStore_noResizeDue _ _ _ _ _ hL2 hNo2 hC
                dsimp only at h
                cases hL3 : lookupTcb Zc server with
                | none => rw [hL3] at h; cases h
                | some st3 =>
                  rw [hL3] at h
                  dsimp only at h
                  cases hC3 : storeObject server.toObjId _ Zc with
                  | error e => rw [hC3] at h; cases h
                  | ok p =>
                    obtain ⟨⟨⟩, Zd⟩ := p
                    rw [hC3] at h
                    cases h
                    show (markKeyChangeFrom _ _ _).objects.noResizeDue
                    rw [markKeyChangeFrom_objects, markKeyChangeFrom_objects]
                    exact tcbStore_noResizeDue _ _ _ _ _ hL3 hNo3 hC3

theorem applyCallDonation_noResizeDue (Z Z' : SystemState) (cV rV : SeLe4n.ValidThreadId)
    (hNo : Z.objects.noResizeDue) (h : applyCallDonation Z cV rV = .ok Z') : Z'.objects.noResizeDue := by
  unfold applyCallDonation at h
  dsimp only at h
  split at h
  · cases h; exact hNo
  · split at h
    · split at h
      · cases h; exact hNo
      · split at h
        · split at h
          · cases h
          · rename_i hD; cases h
            exact donateSchedContext_noResizeDue _ _ _ _ _ hNo hD
        · cases h; exact hNo
    all_goals (cases h; exact hNo)

theorem applyRendezvousCallDonation_noResizeDue (Z : SystemState) (receiver donor : SeLe4n.ThreadId)
    (Z' : SystemState) (hNo : Z.objects.noResizeDue)
    (h : applyRendezvousCallDonation Z receiver donor = .ok Z') : Z'.objects.noResizeDue := by
  unfold applyRendezvousCallDonation applyCallDonationOnCore at h
  split at h
  · split at h
    · cases h
    · rename_i Za hA
      split at h <;> cases h
      · exact migrateSchedContextReplenishment_noResizeDue _ _ _ _ (applyCallDonation_noResizeDue _ _ _ _ hNo hA)
      · exact applyCallDonation_noResizeDue _ _ _ _ hNo hA
  · cases h

theorem replyRecvHolderDeschedule_answer (Z : SystemState) (tid holder : SeLe4n.ThreadId) :
    replyRecvHolderDeschedule tid holder (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      (replyRecvHolderDeschedule tid holder Z).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  unfold replyRecvHolderDeschedule
  split
  · rfl
  · unfold descheduleAtPlacement descheduleAt
    rw [placedCoreOf?_answer]
    cases placedCoreOf? Z holder with
    | none => rfl
    | some k => exact removeRunnableOnCore_answer r ρ μ id κ Z holder k

/-- **The post-receive donation commutes with the answer.** -/
theorem replyRecvPostReceiveDonation_answer (tid rs nt : SeLe4n.ThreadId) (ec : CoreId)
    (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) :
    replyRecvPostReceiveDonation tid rs nt ec ret? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      (replyRecvPostReceiveDonation tid rs nt ec ret? Z).map
        (fun p => (p.1, p.2.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ))) := by
  unfold replyRecvPostReceiveDonation
  rw [rendezvousDequeuedCall_answer]
  cases ret? with
  | none =>
    dsimp only
    split
    · rw [applyRendezvousCallDonation_answer r ρ μ κ Z tid nt hNo]
      cases hA : applyRendezvousCallDonation Z tid nt with
      | error e => rfl
      | ok Za =>
        dsimp only [Except.map]
        rw [propagatePipChainCrossCore_answer r ρ μ id κ Za rs ec (applyRendezvousCallDonation_noResizeDue _ _ _ _ hNo hA)]
    · dsimp only [Except.map]
      rw [propagatePipChainCrossCore_answer r ρ μ id κ Z rs ec hNo]
  | some p =>
    obtain ⟨scId, holder⟩ := p
    dsimp only
    split
    · rw [replyRecvHolderDeschedule_answer, applyRendezvousCallDonation_answer r ρ μ κ _ tid nt
        (replyRecvHolderDeschedule_noResizeDue _ _ _ hNo)]
      cases hA : applyRendezvousCallDonation (replyRecvHolderDeschedule tid holder Z) tid nt with
      | error e => rfl
      | ok Za =>
        dsimp only [Except.map]
        rw [propagatePipChainCrossCore_answer r ρ μ id κ Za rs ec
          (applyRendezvousCallDonation_noResizeDue _ _ _ _ (replyRecvHolderDeschedule_noResizeDue _ _ _ hNo) hA)]
    · dsimp only [Except.map]
      have hD : descheduleAtPlacement (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) holder =
          (descheduleAtPlacement Z holder).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
        unfold descheduleAtPlacement descheduleAt
        rw [placedCoreOf?_answer]
        cases placedCoreOf? Z holder with
        | none => rfl
        | some k => exact removeRunnableOnCore_answer r ρ μ id κ Z holder k
      rw [hD, propagatePipChainCrossCore_answer r ρ μ id κ _ rs ec (descheduleAtPlacement_noResizeDue _ _ hNo)]

end PostReceive
section PostReceiveFrame

theorem updatePipBoostOnCore_answerReadsKept (c : SeLe4n.ThreadId) (s : SystemState) (k : CoreId)
    (t : SeLe4n.ThreadId) (hNo : s.objects.noResizeDue) :
    answerReadsKept c s (PriorityInheritance.updatePipBoostOnCore s k t) := by
  rw [PriorityInheritance.updatePipBoostOnCore_eq_impl]
  unfold PriorityInheritance.updatePipBoostOnCoreImpl
  split
  · dsimp only
    split
    · exact .refl _
    · have h1 := updateTcb_answerReadsKept c t s
        (fun x => { x with pipBoostCode := PriorityInheritance.computeMaxWaiterCode s t }) hNo (fun _ _ => rfl)
      rw [answerReadsKept_iff_objects, markKeyChangeParts_objects, ← answerReadsKept_iff_objects]
      split
      · exact h1.trans (answerReadsKept_of_agreeOffRunLinks
          (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ _ _ _))
      · exact h1
  · exact .refl _

theorem propagatePipChainCrossCore_answerReadsKept (c : SeLe4n.ThreadId) (s : SystemState) (t : SeLe4n.ThreadId)
    (ec : CoreId) (hNo : s.objects.noResizeDue) :
    answerReadsKept c s (PriorityInheritance.propagatePipChainCrossCore s t ec).1 := by
  rw [PriorityInheritance.propagatePipChainCrossCore_eq_walks]
  dsimp only
  generalize s.objects.size = fuel
  induction fuel generalizing s t with
  | zero => exact .refl _
  | succ n ih =>
    unfold PriorityInheritance.propagatePipChainStateWalk
    split
    · exact (updatePipBoostOnCore_answerReadsKept c s _ t hNo).trans
        (ih _ _ (updatePipBoostOnCore_noResizeDue _ _ _ hNo))
    · exact updatePipBoostOnCore_answerReadsKept c s _ t hNo

theorem descheduleAtPlacement_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState) (t : SeLe4n.ThreadId) :
    answerReadsKept c Z (descheduleAtPlacement Z t) := by
  unfold descheduleAtPlacement descheduleAt
  cases placedCoreOf? Z t with
  | none => exact .refl _
  | some k => exact removeRunnableOnCore_answerReadsKept c Z t k

theorem replyRecvHolderDeschedule_answerReadsKept (c tid holder : SeLe4n.ThreadId) (Z : SystemState) :
    answerReadsKept c Z (replyRecvHolderDeschedule tid holder Z) := by
  unfold replyRecvHolderDeschedule
  split
  · exact .refl _
  · exact descheduleAtPlacement_answerReadsKept c Z holder

theorem storeDonationFramePush_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (scId : SeLe4n.SchedContextId) (pushRid : SeLe4n.ReplyId) (pushReply : Reply) (old? : Option SeLe4n.ReplyId)
    (hP : Z.getReply? pushRid ≠ none) (hNo : Z.objects.noResizeDue)
    (h : storeDonationFramePush scId pushRid pushReply old? Z = .ok Z') : answerReadsKept c Z Z' := by
  unfold storeDonationFramePush at h
  split at h
  · cases h
  · cases hR : Z.getReply? pushRid with
    | none => exact absurd hR hP
    | some x =>
      have hk := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
      rw [storeObject_eq_of_leaves (storeLeaves_reply hR _)] at h
      have hNo1 := fun o => insert_present_noResizeDue Z pushRid.toObjId _ o hk hNo
      have hF1 := fun (y : Reply) => insert_answerReadsKept c Z pushRid.toObjId _ (.reply y) hk hNo (fun _ => rfl)
      dsimp only at h
      cases old? with
      | none => cases h; exact hF1 _
      | some old =>
        dsimp only at h
        split at h
        · cases h
        · rename_i oldR hO
          cases hS : storeObject old.toObjId (.reply { oldR with next := some (.frame pushRid) }) _ with
          | error e => rw [hS] at h; cases h
          | ok p =>
            obtain ⟨⟨⟩, Zb⟩ := p
            rw [hS] at h; cases h
            exact (hF1 _).trans (storeObject_answerReadsKept c _ _ _ _ _
              ((SystemState.getReply?_eq_some_iff _ _ _).mp hO) (hNo1 _) (by intro; rfl) hS)

theorem donateSchedContext_answerReadsKept (c : SeLe4n.ThreadId) (Z Z' : SystemState)
    (client server : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (hNo : Z.objects.noResizeDue)
    (h : donateSchedContext Z client server scId = .ok Z') : answerReadsKept c Z Z' := by
  unfold donateSchedContext at h
  cases hS : Z.getSchedContext? scId with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h
    dsimp only at h
    split at h
    · cases h
    · cases hL : lookupTcb Z client with
      | none => rw [hL] at h; cases h
      | some ct =>
        rw [hL] at h
        dsimp only at h
        cases hP : donationPushFrame? Z ct with
        | error e => rw [hP] at h; cases h
        | ok q =>
          obtain ⟨pushRid, pushReply⟩ := q
          obtain ⟨-, hR, -⟩ := donationPushFrame?_ok Z ct pushRid pushReply hP
          rw [hP] at h
          dsimp only at h
          cases hAd : donationPushRefusal? Z server sc.scReply pushRid
          case some => rw [hAd] at h; cases h
          rw [hAd] at h
          dsimp only at h
          rw [storeObject_eq_of_leaves (storeLeaves_schedContext hS _)] at h
          have hNo1 := fun o => insert_present_noResizeDue Z _ _ o (objects_of_getSchedContext? hS) hNo
          have hF1 := fun (y : SchedContext) => insert_answerReadsKept c Z _ _ (.schedContext y)
            (objects_of_getSchedContext? hS) hNo (fun _ => rfl)
          dsimp only at h
          cases hF : storeDonationFramePush scId pushRid pushReply sc.scReply _ with
          | error e => rw [hF] at h; cases h
          | ok Zb =>
            rw [hF] at h
            have hPr : ∀ y : SchedContext, SystemState.getReply?
                { Z with objects := (Z.objects.insert scId.toObjId (.schedContext y)) } pushRid ≠ none := by
              intro y; rw [getReply?_after_schedContext_store Z scId sc _ hS hNo, hR]; simp
            have hNo2 := storeDonationFramePush_noResizeDue _ _ scId pushRid pushReply sc.scReply (hPr _) (hNo1 _) hF
            have hF2 := (hF1 _).trans (storeDonationFramePush_answerReadsKept c _ _ scId pushRid pushReply
              sc.scReply (hPr _) (hNo1 _) hF)
            dsimp only at h
            cases hL2 : lookupTcb Zb client with
            | none => rw [hL2] at h; cases h
            | some ct2 =>
              rw [hL2] at h
              dsimp only at h
              cases hC : storeObject client.toObjId _ Zb with
              | error e => rw [hC] at h; cases h
              | ok p =>
                obtain ⟨⟨⟩, Zc⟩ := p
                rw [hC] at h
                have hNo3 := tcbStore_noResizeDue _ _ _ _ _ hL2 hNo2 hC
                have hF3 := hF2.trans (tcbStore_answerReadsKept c _ _ _ _ _ hL2 hNo2 (by rfl) hC)
                dsimp only at h
                cases hL3 : lookupTcb Zc server with
                | none => rw [hL3] at h; cases h
                | some st3 =>
                  rw [hL3] at h
                  dsimp only at h
                  cases hC3 : storeObject server.toObjId _ Zc with
                  | error e => rw [hC3] at h; cases h
                  | ok p =>
                    obtain ⟨⟨⟩, Zd⟩ := p
                    rw [hC3] at h
                    cases h
                    refine hF3.trans ((tcbStore_answerReadsKept c _ _ _ _ _ hL3 hNo3 (by rfl) hC3).trans ?_)
                    apply answerReadsKept_of_objects
                    rw [markKeyChangeFrom_objects, markKeyChangeFrom_objects]

theorem applyRendezvousCallDonation_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState)
    (receiver donor : SeLe4n.ThreadId) (Z' : SystemState) (hNo : Z.objects.noResizeDue)
    (h : applyRendezvousCallDonation Z receiver donor = .ok Z') : answerReadsKept c Z Z' := by
  have hA : ∀ cV rV Za, applyCallDonation Z cV rV = .ok Za → answerReadsKept c Z Za := by
    intro cV rV Za h
    unfold applyCallDonation at h
    dsimp only at h
    split at h
    · cases h; exact .refl _
    · split at h
      · split at h
        · cases h; exact .refl _
        · split at h
          · split at h
            · cases h
            · rename_i hD; cases h
              exact donateSchedContext_answerReadsKept c _ _ _ _ _ hNo hD
          · cases h; exact .refl _
      all_goals (cases h; exact .refl _)
  unfold applyRendezvousCallDonation applyCallDonationOnCore at h
  split at h
  · split at h
    · cases h
    · rename_i Za hAD
      split at h <;> cases h
      · exact (hA _ _ _ hAD).trans (migrateSchedContextReplenishment_answerReadsKept c _ _ _ _)
      · exact hA _ _ _ hAD
  · cases h

end PostReceiveFrame

section Tail

theorem replyRecvPostReceiveDonation_noResizeDue_answerReadsKept (c tid rs nt : SeLe4n.ThreadId) (ec : CoreId)
    (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z Z' : SystemState)
    (hNo : Z.objects.noResizeDue) (h : replyRecvPostReceiveDonation tid rs nt ec ret? Z = .ok ((), Z')) :
    Z'.objects.noResizeDue ∧ answerReadsKept c Z Z' := by
  unfold replyRecvPostReceiveDonation at h
  cases ret? with
  | none =>
    dsimp only at h
    split at h
    · cases hA : applyRendezvousCallDonation Z tid nt with
      | error e => rw [hA] at h; cases h
      | ok Za =>
        rw [hA] at h; cases h
        have hNoA := applyRendezvousCallDonation_noResizeDue _ _ _ _ hNo hA
        exact ⟨propagatePipChainCrossCore_noResizeDue _ _ _ hNoA,
          (applyRendezvousCallDonation_answerReadsKept c _ _ _ _ hNo hA).trans
            (propagatePipChainCrossCore_answerReadsKept c _ _ _ hNoA)⟩
    · cases h
      exact ⟨propagatePipChainCrossCore_noResizeDue _ _ _ hNo, propagatePipChainCrossCore_answerReadsKept c _ _ _ hNo⟩
  | some p =>
    obtain ⟨scId, holder⟩ := p
    dsimp only at h
    have hNoD := replyRecvHolderDeschedule_noResizeDue tid holder Z hNo
    split at h
    · cases hA : applyRendezvousCallDonation (replyRecvHolderDeschedule tid holder Z) tid nt with
      | error e => rw [hA] at h; cases h
      | ok Za =>
        rw [hA] at h; cases h
        have hNoA := applyRendezvousCallDonation_noResizeDue _ _ _ _ hNoD hA
        exact ⟨propagatePipChainCrossCore_noResizeDue _ _ _ hNoA,
          ((replyRecvHolderDeschedule_answerReadsKept c tid holder Z).trans
            (applyRendezvousCallDonation_answerReadsKept c _ _ _ _ hNoD hA)).trans
            (propagatePipChainCrossCore_answerReadsKept c _ _ _ hNoA)⟩
    · cases h
      have hNoP := descheduleAtPlacement_noResizeDue Z holder hNo
      exact ⟨propagatePipChainCrossCore_noResizeDue _ _ _ hNoP,
        (descheduleAtPlacement_answerReadsKept c Z holder).trans
          (propagatePipChainCrossCore_answerReadsKept c _ _ _ hNoP)⟩

theorem applyReceiveLegPipHandoff_answer (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat) (Z : SystemState)
    (receiver dequeued walked : SeLe4n.ThreadId) (ec : CoreId) (hNo : Z.objects.noResizeDue) :
    applyReceiveLegPipHandoff (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) receiver dequeued walked ec =
      (applyReceiveLegPipHandoff Z receiver dequeued walked ec).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  unfold applyReceiveLegPipHandoff applyReceiverPipHandoff
  rw [rendezvousDequeuedCall_answer]
  split
  · rfl
  · split
    · exact propagatePipChainCrossCore_answer r ρ μ id κ Z receiver ec hNo
    · rfl

theorem applyReceiveLegPipHandoff_answerReadsKept (c : SeLe4n.ThreadId) (Z : SystemState)
    (receiver dequeued walked : SeLe4n.ThreadId) (ec : CoreId) (hNo : Z.objects.noResizeDue) :
    answerReadsKept c Z (applyReceiveLegPipHandoff Z receiver dequeued walked ec) := by
  unfold applyReceiveLegPipHandoff applyReceiverPipHandoff
  split
  · exact .refl _
  · split
    · exact propagatePipChainCrossCore_answerReadsKept c Z receiver ec hNo
    · exact .refl _

theorem endpointReceiveDualWithCapsOnCore_noResizeDue (Z : SystemState) (k : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId) (ec : CoreId) (hNo : Z.objects.noResizeDue) :
    (endpointReceiveDualWithCapsOnCore k tid rid ec Z).1.objects.noResizeDue := by
  have hNo1 := endpointReceiveDualOnCore_noResizeDue Z k tid rid ec hNo
  unfold endpointReceiveDualWithCapsOnCore
  dsimp only
  cases hR : endpointReceiveDualOnCore k tid rid ec Z with
  | mk Za res =>
    rw [hR] at hNo1
    cases res with
    | error e => exact hNo1
    | ok p =>
      obtain ⟨sid, sgi⟩ := p
      dsimp only
      split
      · exact hNo1
      · cases hT : receiveTransferCaps (receiveCapRequest Z k) (some k) (receiverCapTarget? Z tid) Za with
        | error e => exact hNo1
        | ok q =>
          obtain ⟨sm, Zb⟩ := q
          exact (receiveTransferCaps_answerReadsKept tid _ _ _ hNo1 hT).1

end Tail

end SeLe4n.Kernel
